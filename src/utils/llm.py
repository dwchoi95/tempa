"""Single place where LLM API calls happen.

Every arm (builder, fallback, per-submission baselines, LSGen reproduction)
goes through :func:`complete`, so token accounting, pricing and latency are
measured identically everywhere and no other module needs a provider SDK.

Backends are selected by model name and resolved lazily, so importing this
module never requires a provider package or an API key.
"""
from __future__ import annotations

import os
import re
import time
from dataclasses import dataclass

from src.utils.metrics import count_tokens, cost_usd


@dataclass
class Completion:
    """One prompt/response exchange with everything the metrics need."""
    text: str
    model: str
    in_tokens: int
    out_tokens: int
    seconds: float
    usd: float
    cached_read: int = 0
    cached_write: int = 0
    usd_paid: float | None = None     # what was billed, when it differs from list price

    @property
    def code(self) -> str | None:
        return extract_code(self.text)


def extract_code(text: str) -> str | None:
    """First fenced Python block, else the whole text if it parses as code."""
    if text is None:
        return None
    m = re.search(r"```(?:python|py)?\s*\n(.*?)```", text, re.S)
    if m:
        return m.group(1).strip("\n")
    stripped = text.strip()
    if stripped and not stripped.startswith("```"):
        import ast
        try:
            ast.parse(stripped)
            return stripped
        except SyntaxError:
            return None
    return None


def complete(prompt: str, model: str = "claude-sonnet-5", *, system: str | None = None,
             max_tokens: int = 64000, temperature: float | None = 0.0,
             cache_prefix: str | None = None, batch: bool = False) -> Completion:
    """Send one prompt, return the response with usage accounting.

    ``cache_prefix`` marks a shared prefix for provider prompt caching; it is
    accounted separately so cached and uncached arms stay comparable.
    ``batch`` sends the same request through the provider's batch endpoint and
    waits for it: the same model and parameters at half the price, billed in
    ``usd_paid``, while ``usd`` stays at list price so every build is priced
    alike.
    """
    t0 = time.time()
    last = None
    for attempt in range(5):
        try:
            if model.startswith("claude"):
                text, usage = _anthropic(prompt, model, system, max_tokens, temperature,
                                         cache_prefix, batch)
            elif model.startswith("gpt"):
                text, usage = _openai(prompt, model, system, max_tokens, temperature, batch)
            elif model.startswith("local:"):
                text, usage = _local(prompt, model.split(":", 1)[1], system, max_tokens, temperature)
            else:
                raise ValueError(f"unknown model backend: {model}")
            break
        except Exception as e:                       # noqa: BLE001
            name = type(e).__name__
            transient = any(k in name for k in (
                "RateLimit", "Overloaded", "InternalServer", "APIConnection",
                "ServiceUnavailable", "Timeout", "APIStatus",
                "RemoteProtocol", "ReadError"))      # dropped streaming connections
            if not transient or attempt == 4:
                raise
            last = e
            time.sleep(2 ** (attempt + 1))           # 2,4,8,16s backoff
    del last
    elapsed = time.time() - t0
    in_tok = usage.get("in", count_tokens(prompt) + (count_tokens(system) if system else 0))
    out_tok = usage.get("out", count_tokens(text))
    price_key = model.split(":", 1)[-1] if model.startswith("local:") else model
    usd = cost_usd(in_tok, out_tok, price_key, cache_read=usage.get("cache_read", 0),
                   cache_write=usage.get("cache_write", 0))
    return Completion(
        text=text, model=model, in_tokens=in_tok, out_tokens=out_tok, seconds=elapsed,
        usd=usd, cached_read=usage.get("cache_read", 0), cached_write=usage.get("cache_write", 0),
        usd_paid=usd * BATCH_DISCOUNT if batch else None)


# ----------------------------------------------------------------- backends
BATCH_DISCOUNT = 0.5          # both providers bill batch requests at half price
BATCH_POLL = 30               # seconds between status checks


def _deprecates_temperature(model_id: str) -> bool:
    """True for Claude models that reject the `temperature` parameter."""
    return model_id.startswith(("claude-sonnet-5", "claude-opus-4", "claude-fable"))


def _anthropic(prompt, model, system, max_tokens, temperature, cache_prefix, batch=False):
    import anthropic
    client = anthropic.Anthropic(api_key=os.environ["ANTHROPIC_API_KEY"])
    if cache_prefix:
        content = [{"type": "text", "text": cache_prefix,
                    "cache_control": {"type": "ephemeral"}},
                   {"type": "text", "text": prompt}]
    else:
        content = prompt
    model_id = model
    kwargs = {"model": model_id, "max_tokens": max_tokens,
              "messages": [{"role": "user", "content": content}]}
    if system:
        kwargs["system"] = system
    # Newer Claude models (sonnet-5, opus-4.x) deprecate `temperature`
    # and reject it; only the older families still accept it.
    if temperature is not None and not _deprecates_temperature(model_id):
        kwargs["temperature"] = temperature
    if batch:
        resp = _anthropic_batch(client, kwargs)
    # Stream when the output budget is large: the SDK refuses a non-streaming
    # call whose worst-case generation could exceed its request timeout.
    elif max_tokens > 8192:
        with client.messages.stream(**kwargs) as s:
            resp = s.get_final_message()
    else:
        resp = client.messages.create(**kwargs)
    u = resp.usage
    # With extended thinking the first block is a ThinkingBlock; concatenate the
    # text blocks and ignore the rest. Thinking tokens are billed as output and
    # are already included in u.output_tokens, so cost stays accurate.
    text = "".join(b.text for b in resp.content if getattr(b, "type", None) == "text")
    return text, {
        "in": u.input_tokens, "out": u.output_tokens,
        "cache_read": getattr(u, "cache_read_input_tokens", 0) or 0,
        "cache_write": getattr(u, "cache_creation_input_tokens", 0) or 0}


def _anthropic_batch(client, params):
    """One request through the Message Batches API; waits for the result."""
    b = client.messages.batches.create(requests=[{"custom_id": "q", "params": params}])
    while b.processing_status != "ended":
        time.sleep(BATCH_POLL)
        b = client.messages.batches.retrieve(b.id)
    for r in client.messages.batches.results(b.id):
        if r.result.type == "succeeded":
            return r.result.message
        raise RuntimeError(f"batch request {r.result.type}: {getattr(r.result, 'error', '')}")
    raise RuntimeError("batch returned no result")


def _openai(prompt, model, system, max_tokens, temperature, batch=False):
    from openai import OpenAI
    client = OpenAI(api_key=os.environ["OPENAI_API_KEY"])
    model_id = model
    msgs = ([{"role": "system", "content": system}] if system else []) + \
           [{"role": "user", "content": prompt}]
    # GPT-5 series takes `max_completion_tokens`, not `max_tokens`,
    # and support only the default temperature.
    is_gpt5 = model_id.startswith("gpt-5")
    kwargs = {"model": model_id, "messages": msgs}
    kwargs["max_completion_tokens" if is_gpt5 else "max_tokens"] = max_tokens
    if temperature is not None and not is_gpt5:
        kwargs["temperature"] = temperature
    if batch:
        body = _openai_batch(client, kwargs)
        u = body["usage"]
        return body["choices"][0]["message"]["content"], {
            "in": u["prompt_tokens"], "out": u["completion_tokens"],
            "cache_read": (u.get("prompt_tokens_details") or {}).get("cached_tokens", 0) or 0}
    resp = client.chat.completions.create(**kwargs)
    u = resp.usage
    return resp.choices[0].message.content, {
        "in": u.prompt_tokens, "out": u.completion_tokens,
        "cache_read": getattr(getattr(u, "prompt_tokens_details", None),
                              "cached_tokens", 0) or 0}


def _openai_batch(client, body):
    """One request through the Batch API; waits for the result's body."""
    import io
    import json
    line = json.dumps({"custom_id": "q", "method": "POST",
                       "url": "/v1/chat/completions", "body": body})
    f = client.files.create(file=("q.jsonl", io.BytesIO(line.encode())), purpose="batch")
    b = client.batches.create(input_file_id=f.id, endpoint="/v1/chat/completions",
                              completion_window="24h")
    while b.status not in ("completed", "failed", "expired", "cancelled"):
        time.sleep(BATCH_POLL)
        b = client.batches.retrieve(b.id)
    if b.status != "completed" or not b.output_file_id:
        raise RuntimeError(f"batch {b.status}: {b.errors}")
    out = json.loads(client.files.content(b.output_file_id).text.splitlines()[0])
    if out.get("error") or out["response"]["status_code"] != 200:
        raise RuntimeError(f"batch request failed: {out.get('error') or out['response']}")
    return out["response"]["body"]


def _local(prompt, model, system, max_tokens, temperature):
    """Self-hosted open model via MLX (Apple silicon). Cost is time, not tokens."""
    from mlx_lm import generate, load
    mdl, tok = _local_cache(model)
    full = (system + "\n\n" if system else "") + prompt
    text = generate(mdl, tok, prompt=full, max_tokens=max_tokens, verbose=False)
    return text, {}


_LOCAL_CACHE: dict = {}


def _local_cache(model):
    if model not in _LOCAL_CACHE:
        from mlx_lm import load
        _LOCAL_CACHE[model] = load(model)
    return _LOCAL_CACHE[model]
