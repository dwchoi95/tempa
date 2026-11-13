# PyDex baseline (reproduction)

Faithful reproduction of the **semantic phase** of PyDex (Zhang et al.,
OOPSLA 2024), driven by our own models so ATT/InT/OuT/$API are measured
identically to TEMPA.

- **Prompt**: the multimodal zero-shot prompt of Fig. 6, laid out exactly as in
  the paper (buggy program first, then description, then tests, then
  `### Correct Program ###`); the operative arm is the few-shot prompt of
  Fig. 7: the bank pairs each pool buggy program with its structurally nearest
  correct solution from the reference pool, and the 3 most similar shots by
  failure-vector (1 - normalized Hamming) similarity precede each query (the
  target is never its own shot).
- **K candidates**: each prompt yields K=10 sampled candidates (default
  provider temperature), every call billed and timed regardless of outcome.
- **Oracle + selection**: candidates run on the full suite; any failure
  discards the candidate; the minimum token-edit-distance survivor is the
  repair. No iterative refinement exists in the semantic phase.

Driver: `python3 run.py pydex --problem <pid> --model {claude-haiku,gpt-nano}`
writes `results/<ver>/<pid>/{pydex,pydex_pc}.csv` + summary rows.
