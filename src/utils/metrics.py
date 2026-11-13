"""Evaluation metrics: RR, RPS, ATT, InT, OuT, Cost.

RPS follows the *reference implementation* of Refactory (Hu et al., ASE 2019),
not a paraphrase of the paper: patch size is the Zhang-Shasha tree edit
distance between the buggy and repaired ASTs, summed over the union of their
function names, and normalized by the AST node count of the buggy program.

    patch_size = sum_f  TED(AST(buggy.f), AST(repaired.f))     unit relabel cost
    patch_size = 1  if patch_size == 0 but the sources differ
    RPS        = patch_size / max(1, ast_size(buggy))

Node labels replicate Refactory's ``acc_str_node``: identifier / name /
argument / literal when present, else the AST class name, with ``Module``,
``Load`` and ``Store`` collapsed into their parent.
"""
from __future__ import annotations

import ast

try:
    from zss import Node, simple_distance
    _HAVE_ZSS = True
except ImportError:  # pragma: no cover - metrics degrade, harness still runs
    _HAVE_ZSS = False


# ------------------------------------------------------------------ RPS
def _label(node: ast.AST) -> str:
    for attr in ("id", "name", "arg"):
        if hasattr(node, attr):
            return str(getattr(node, attr))
    if isinstance(node, ast.Constant):
        v = node.value
        return f"'{v}'" if isinstance(v, str) else str(v)
    cls = node.__class__.__name__
    return "" if cls in ("Module", "Load", "Store") else cls


def _visit(node: ast.AST, parent: "Node") -> None:
    label = _label(node)
    target = parent if label == "" else Node(label)
    if label != "":
        parent.addkid(target)
    for _, value in ast.iter_fields(node):
        items = value if isinstance(value, list) else [value]
        for item in items:
            if isinstance(item, ast.AST):
                _visit(item, target)


def _tree(src: str) -> "Node":
    root = Node("root")
    _visit(ast.parse(src), root)
    return root


def _size(node: "Node") -> int:
    return 1 + sum(_size(k) for k in node.children)


def func_map(src: str) -> dict[str, str]:
    """Top-level functions by name; module-level code under the key ``""``."""
    try:
        tree = ast.parse(src)
    except SyntaxError:
        return {}
    out, rest = {}, []
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            out[node.name] = ast.get_source_segment(src, node) or ""
        else:
            seg = ast.get_source_segment(src, node)
            if seg:
                rest.append(seg)
    if rest:
        out[""] = "\n".join(rest)
    return out


def ast_size(src: str) -> int:
    """Node count per Refactory's ``zss_ast_size``.

    The synthetic ``root`` node is *counted*, matching the reference
    implementation (verified against it case by case).
    """
    total = 0
    for code in func_map(src).values():
        try:
            total += _size(_tree(code))
        except SyntaxError:
            continue
    return total


def rps(buggy: str, repaired: str) -> float:
    """Relative patch size, per Refactory's reference implementation."""
    if not _HAVE_ZSS:
        raise RuntimeError("zss is required for RPS; pip install zss")
    a, b = func_map(buggy), func_map(repaired)
    total = 0
    for name in set(a) | set(b):
        ca, cb = a.get(name, ""), b.get(name, "")
        try:
            ta = _tree(ca) if ca.strip() else Node("root")
            tb = _tree(cb) if cb.strip() else Node("root")
        except SyntaxError:
            return 1.0
        total += simple_distance(ta, tb, label_dist=lambda x, y: 0 if x == y else 1)
    if total == 0 and buggy != repaired:
        total = 1
    return total / max(1, ast_size(buggy))


# ------------------------------------------------------------------ tokens
_CHARS_PER_TOKEN = 3.6
MODE = "approx-chars/3.6"

try:  # exact counts when a tokenizer is available offline
    import tiktoken as _tk
    _ENC = _tk.get_encoding("cl100k_base")
    MODE = "tiktoken/cl100k_base"
except Exception:  # pragma: no cover
    _ENC = None


def count_tokens(text: str) -> int:
    if _ENC is not None:
        return len(_ENC.encode(text))
    return int(len(text) / _CHARS_PER_TOKEN + 0.5)


# ------------------------------------------------------------------ cost
PRICES = {  # USD per million tokens, (input, output)
    "claude-sonnet-5": (2.00, 10.00),    # introductory pricing through 2026-08-31
    "gpt-5.4-mini": (0.75, 4.50),        # cached input $0.075 = 0.1x
    "gpt-4o": (2.50, 10.00),
    "gpt-4o-mini": (0.15, 0.60),
    "qwen2.5-coder-7b-local": (0.0, 0.0),  # self-hosted: measured separately
}
CACHE_READ_MULT, CACHE_WRITE_MULT = 0.1, 1.25


def cost_usd(in_tokens: int, out_tokens: int, model: str = "claude-sonnet-5",
             cache_read: int = 0, cache_write: int = 0) -> float:
    """Provider-aware billing. Anthropic reports input_tokens EXCLUDING cache
    reads/writes (separate fields, write 1.25x / read 0.1x); OpenAI reports
    prompt_tokens INCLUDING cached_tokens (reads 0.1x, writes free pre-5.6)."""
    pin, pout = PRICES[model]
    if model.startswith("gpt"):
        uncached = max(0, in_tokens - cache_read)
        return ((uncached + cache_read * CACHE_READ_MULT) * pin
                + out_tokens * pout) / 1e6
    return ((in_tokens + cache_read * CACHE_READ_MULT + cache_write * CACHE_WRITE_MULT) * pin
            + out_tokens * pout) / 1e6


