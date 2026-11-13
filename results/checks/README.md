# Checks behind the paper's numbers

Each directory holds the scripts that one or more of the paper's claims cite, the scripts they import,
and the small result files the numbers come from. Run them from the repository root with CPython 3.13
and `requirements.txt`; no script calls a model API. Each writes its results next to itself.
Runtimes are wall-clock times on a 20-core machine.

Not tracked (`.gitignore`): caches, which only make a rerun faster, and outputs over 5 MB. A script
runs without its cache, only more slowly.

## `running_example/`

The running example of the Introduction and Section 2, the submission `wrong_1_042` of sequential search: the
rule of Figure 1 and the rule it rejects, the repairs of Figure 2 and the two-rule repair of Section 2.2, the correct program it is paired with, what the existing techniques returned for it,
and the type checker's rejection of a rule that guesses a name.

```text
python3 -I results/checks/running_example/check.py       # 5 s -> check.txt
```

## `splits_rules/`

The tools built from the first 10% of a class, on its last quarter (the 40 split tools that Appendix A.2 counts): RR<sub>0.25</sub> with and
without the builder's rules on 1,317 programs of R1–R5 (three orders) and 313 of C1–C5, and
the exact McNemar tests.

```text
python3 -I results/checks/splits_rules/analyze.py        # 11 s -> rows.csv, summary.csv
```

## `baselines/`

The builder's rules against no rules and against Refazer's (Section 4.4; Appendix B.4, Table B.2),
on all programs and on those never shown as worked pairs.

```text
python3 -I results/checks/baselines/worked_pairs.py      # 19 s -> worked_pairs.csv
python3 -I results/checks/baselines/analyze.py           # 14 s -> rows.csv (7 MB, not tracked), metrics.csv, mcnemar.csv
python3 -I results/checks/baselines/rules_where.py       # 8 s  -> rules_where.txt (Table B.2, the programs never shown as nearest-correct pairs)
python3 -I results/checks/baselines/rules_builds.py      # 1 s  -> rules_builds.txt (the two rebuilds)
```

`analyze.py` runs first: the other two read its `rows.csv`. `worked_pairs.csv` marks the programs
shown to the builder as worked pairs. `baseline_rows.csv` holds the per-program verdicts of PyDex,
LLM_Direct (both as in `results/ablation.csv`) and Refactory (its repair passes T and, on R1–R5,
the held-out suite). `baseline_refazer/` holds the runs of the frozen tool with
Refazer's rules; `compare_with.py` made them (its docstring gives the command; Refazer
needs Mono, and a run takes hours).

## `cf_heldout/`

The independent suite for C1–C6 (Section 4.1; Appendix B.1): generators and reference solutions
written from each problem statement (`gens.py`), 100 inputs per assignment (`suites/`), and every
arm's official-test-passing repairs judged on it. CPU only, no model call.

```text
python3 -I results/checks/cf_heldout/cf_heldout.py all   # 1.5 min -> suites/, rows.csv, shares.csv, report.txt
```

`shares.csv` gives, per arm and builder, the repairs that pass the official tests and how many also
pass the suite.

## `prune/`

Footprint pruning in the rule search, which the locality of the search allows (Corollary 21); the paper
does not report it. Every buggy program and builder, searched without and with pruning.

```text
results/checks/prune/run_all.sh                          # 8 jobs at a time; 30 CPU-hours, at least 6.3 h -> rows/<pid>__<model>.csv
python3 -I results/checks/prune/run.py PID MODEL         # one job; cf_10C: 1 min, cf_125A: 9 min
python3 -I results/checks/prune/analyze.py               # 1 s -> summary.csv
```

## `footprint/`

The footprint theorem on CPython and the footprint lines of every repair (Sections 3.2.2 and 4.2; Appendix A.3).
`run.py` runs every buggy program, traced, and every repair of the six sources on every input, and
writes `cache/` (1.4 GB, not tracked); the three analyses after it read that cache and run `run.py`
first when it is missing.

```text
python3 -I results/checks/footprint/run.py .             # 7 min -> cache/
python3 -I results/checks/footprint/analyze.py .         # 33 s  -> summary.csv (19,635 repairs, 372,056 inputs, 0 violations)
python3 -I results/checks/footprint/footprint_lines.py . # 2 min -> footprint_lines.txt (needs ../baselines/rows.csv)
python3 -I results/checks/footprint/outside_core.py .    # 44 s  -> outside_core.txt
```

Appendix A's checks on the programs, the rules, and the harness (Appendices A.2–A.5):

```text
python3 -I results/checks/footprint/syntax.py .          # 2 s   -> syntax.txt (the syntax the programs use)
python3 -I results/checks/footprint/core_census.py .     # 5 s   -> core_census.txt (what the theorem excludes)
python3 -I results/checks/footprint/keep_audit.py .      # 65 s  -> keep_audit.txt (Keep on every rule and program)
python3 -I results/checks/footprint/static_off.py .      # 4 s   -> static_off.txt, static_off.jsonl (the 106 TRL tools of tools/)
python3 -I results/checks/footprint/static_off_run.py .  # 3 min -> static_off_run.txt, static_off_run.jsonl
python3 -I results/checks/footprint/history.py .         # 11 s  -> history.txt (each test of T+ alone)
```

`keep_audit.py` compares Keep with `rulelang_skip.py` and reads the split tools under `splits_work/`
(`python3 run.py splits make` regenerates them). `history.py` reads the pools of
`../oracle_theory/a4_pool/`.

## `student_fix/`

Footprint lines against the student's own later fix on C1–C6 (Section 4.2; Appendix B.2).

```text
python3 -I results/checks/student_fix/fetch.py .         # network, 11 min -> authors.csv
python3 -I results/checks/student_fix/analyze.py .       # 30 s -> analyze.txt, pairs.csv
python3 -I results/checks/student_fix/own_fix.py         # 6 s -> own_fix.txt
```

`fetch.py` reads Codeforces' public API; `authors.csv` keeps an integer in place of each handle.
`own_fix.py` splits each tool's precision by whether the student's own fix is among the eight
correct programs the transplant may adopt from, and, where it is not, by whether the buggy program or
the own fix is in any of the builder's pairs, which it recomputes with Select (no model call).

## `oracle_theory/`

How far the class is from a wrong label, and the per-program bound with a stated confidence for
Proposition 15 (Appendix A.5).

```text
python3 -I results/checks/oracle_theory/vote_margin.py .      # 4 s -> vote_margin.txt
python3 -I results/checks/oracle_theory/certified.py .        # 2 min (1 s with cache/) -> certified.txt, certified.csv
python3 -I results/checks/oracle_theory/a4_pool.py pool 6     # 10 min, the pools -> a4_pool/<pid>_<model>.jsonl
python3 -I results/checks/oracle_theory/a4_pool.py err 12     # 7 min, err(c) of their candidates -> a4_err/<pid>_<model>.json
python3 -I results/checks/oracle_theory/common.py             # 1 s, checks that its labelling gives a stored T_amp
```

`certified.py` reads the pools of the search in which no candidate passes T+ and their candidates'
err(c) (`a4_pool/`, `a4_err/`, from `a4_pool.py`), and the 20,000 draws of D that `common.py` draws
and labels, cached in `cache/` (18 MB, not tracked).

## `lean_sem/`

The Lean semantics run against CPython 3.13 (`difftest.py`) and against PyCore on the translation
(`coretest.py`), on the 2,970 buggy programs and TEMPA's 4,693 repairs (Appendix A.3, "Mechanization").
Both run `mech/.lake/build/bin/pycore` (`cd mech && lake build`); `PYCORE` names another binary.

```text
python3 -I results/checks/lean_sem/difftest.py .         # -> difftest.txt, difftest.jsonl (1.4 GB, not tracked)
python3 -I results/checks/lean_sem/coretest.py .         # -> coretest.txt, coretest.jsonl (31 MB, not tracked)
python3 -I results/checks/lean_sem/difftest.py . --pid refactory_q5   # one assignment: 7 s
python3 -I results/checks/lean_sem/coretest.py . --pid refactory_q5   # 2 s
```

The full runs were not timed here. A batch of programs that reaches the 30-minute wall-clock limit
is run again one program at a time, with 5 minutes each for `difftest.py` and 10 for `coretest.py`,
and a few programs of C1–C6 reach it.

`difftest.py` caches CPython's runs in `cpython_cache.jsonl` (1.3 GB, not tracked), which
`coretest.py` reuses; `coretest.py` runs CPython itself on a program `difftest.py` has not run. With
`--pid`, both write that assignment's results in place of the full ones. `census.py` counts what the
programs use (`census.txt`), `gen_tests.py` writes `mech/SurfSemTests.lean` from `cases/`, and
`setfuzz.py N SEED` checks set iteration order on random programs.

## `lean_cls/`

The mechanized classification of every name against CPython's symbol tables (Appendix A.3,
"Mechanization"). Needs CPython 3.11 as `python3.11` (`PYTHON311` names another).

```text
python3 -I results/checks/lean_cls/surf_cls.py .                # 12 s -> surf_cls.txt
python3 -I results/checks/lean_cls/surf_cls.py . --fuzz 100000  # 91 s -> surf_cls_fuzz.txt
```

## `iid/`

Whether each draw of a builder's generator depends on the random stream alone (Appendix A.5, "The
assumption on draws"; the 60,000 draws replayed in a fresh process).

```text
python3 -I results/checks/iid/replay.py .                # 4 min -> replay.txt
```

## `rows/`

The per-program rows behind Section 4's comparisons, and the scripts that build them. Each script reads
the logs under `results/` and `tools/`, writes its rows next to itself, and calls no model.

```text
PYTHONPATH=. python3 results/checks/rows/refactory_oracle.py   # needs Refactory's code in baselines/refactory -> refactory_oracle.csv
python3 -I results/checks/rows/gate/a2_gate.py           # 2 s with cache/ -> A2_rows.csv, A2_gate.csv, A2_mcnemar.csv
python3 -I results/checks/rows/oos/a1_oos.py             # 2 s with cache/ -> A1_rows.csv (6.5 MB, not tracked), A1_metrics.csv, A1_mcnemar.csv
python3 -I results/checks/rows/stages/select_report.py   # 2 s -> rand_rows.csv, rand_cost.csv (TEMPA^rand)
python3 -I results/checks/rows/stages/python_rows.py     # 1 s -> python_rows.csv (TEMPA^Python, from ../python_rules/run/r0)
python3 -I results/checks/rows/stages/stage_rows.py      # 1 s -> stage_rows.csv (Table 4, Figure 8)
python3 -I results/checks/rows/stages/gap_bootstrap.py   # 1 s -> gap_bootstrap.txt (App. B.4, paired bootstrap of the model gap)
python3 -I results/checks/rows/oos/refactory_split.py    # 1 s -> refactory_split.txt (App. B.1, Refactory's 495 unrepaired programs)
python3 -I results/checks/rows/tokens.py                 # 1 s -> tokens.txt (Section 4.3, tokens PyDex and TEMPA generate)
python3 -I results/checks/rows/rule_traits/recurring.py  # 1 s -> recurring.json (Figure 10, bottom)
python3 -I results/checks/rows/rule_traits/rules_used.py  # 4 s -> rules_used.txt (Section 4.5, rules written, passing, used)
```

They run in this order: `a1_oos.py` reads `A2_rows.csv` and `refactory_oracle.csv`, and the stage scripts
read `A1_rows.csv` and `../baselines/rows.csv`, `refactory_split.py` reads `A1_rows.csv`, and `gap_bootstrap.py` reads `stage_rows.csv` and `python_rows.csv`. Without `cache/`, `a2_gate.py` and `a1_oos.py` run the
held-out suites again, which takes longer. `recurring.py` sorts the used rules into kinds by name and
rewrite, with the rules checked by hand listed in it.

## `python_rules/`

TEMPA^Python, the builder's rules written as Python functions (Section 4.4; Appendix A.2, "Unbound
names"; Appendix B.4). `tools_python/` holds the Python tools of the three builds and `run/` their runs;
`filter/` holds the 33 tools rebuilt with TRL's checks as a filter and their runs. `run_python.py`,
`filter/build_filter.py`, and `filter/run_filter.py` built and ran them and call the builder model; the
analyses below do not.

```text
python3 -I results/checks/python_rules/compare.py .        # 41 s  -> compare.txt, compare.csv (Figure B.3)
python3 -I results/checks/python_rules/compare.py . filter # 30 s  -> filter/compare.txt
python3 -I results/checks/python_rules/rule_size.py .      # 1 s   -> rule_size.txt (lines per rule, build cost)
python3 -I results/checks/python_rules/audit.py .          # 2 min -> audit.txt, audit.json (unbound names)
```

## `figures/`

Figures 6–10 and Figure B.3, drawn from the rows above (needs Ghostscript, `gs`, to embed the fonts).

```text
python3 -I results/checks/figures/figs_rq.py             # 3 s -> paper/figures/fig_{rq1,growth,ablation,rq4_a,rules_compact,rq2}.pdf
```
