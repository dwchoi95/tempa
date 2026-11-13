# TEMPA: Program Repair via Typed Error Models for Programming Assignments

This is the artifact of the paper. TEMPA has an LLM write each assignment's error model once,
as repair rules in TRL, the TEMPA Rule Language; it then repairs submissions with those rules,
with code transplanted from the class's correct programs, and with an API call only as a
fallback. The artifact holds TEMPA's implementation, the benchmark, the tools built per
assignment, the per-submission logs of every run, the scripts that recompute every number of
the paper from those logs, and the Lean 4 mechanization of the footprint theorem.

| Directory | Contents | Paper |
|---|---|---|
| `src/` | TEMPA (`core/`: Select, TRL, Amplify, Repair; `runner/`: test harness; `experiments/`: one driver per experiment, dispatched by `run.py`) | Section 3 |
| `mech/` | the Lean 4 development: PyCore, the Python semantics, the translation, the footprint theorem | Section 3.2.2, Appendix A.3 |
| `benchmark/<pid>/` | the 11 assignments: buggy and correct programs, tests T, held-out suites, the builders' generators and amplified tests | Section 4.1, Table 1 |
| `tools/` | the built tools: `<pid>/<model>/fixer.rules` (main build), `rebuild/`, `splits/`, `select_rand/` | Sections 4.2–4.5 |
| `results/` | per-submission logs of every run, one CSV per tool and assignment | Section 4 |
| `results/checks/` | the scripts that recompute each number from the logs, with their outputs (see its `README.md`) | Sections 3–4, Appendices A–B |
| `baselines/pydex/` | our re-implementation of PyDex's few-shot phase | Section 4.1 |

In file names and result columns, `TEMPA_LF` is TEMPA, `TEMPA_L` is TEMPA<sup>−fallback</sup>,
and the ablation arms are named as in `results/checks/rows/stages/stage_rows.py`.
Assignment ids: R1–R5 are `refactory_q1`–`q5`; C1–C6 are `cf_110A`, `cf_131A`, `cf_1011B`,
`cf_125A`, `cf_11B`, `cf_10C`.

## Requirements

What we ran on:

```text
Mac Studio, Apple M1 Ultra (20-core CPU), 64 GB memory, macOS 26.7; no GPU
CPython 3.13.7 with requirements.txt; Lean 4 v4.35.0 (mech/lean-toolchain, no library beyond Lean's core)
Ghostscript (gs) to draw the figures; CPython 3.11 as python3.11 for results/checks/lean_cls/
```

The repository takes about 430 MB. Modes A and B below need no API key and no
network. Only mode C calls a model (keys in `.env`, see `.env.example`).

## Getting Started (about 5 minutes)

```sh
python3 -m venv .venv && . .venv/bin/activate        # CPython 3.13
pip install -r requirements.txt

python3 -I results/checks/running_example/check.py    # 12 s
python3 -I results/checks/rows/table3.py              # 1 s
python3 -I results/checks/rows/stages/stage_rows.py   # 1 s
python3 -I results/checks/figures/figs_rq.py          # 3 s
```

Expected:

- `check.py` writes `results/checks/running_example/check.txt`, whose fourth line is the
  repair of Figure 2d: `Figure 2d: rules ['compare_x_to_elem_strict_lt',
  'return_len_plus_one_to_len', 'generic_shift_index'] RPS 0.1296 ...`.
- `table3.py` prints Table 3; its TEMPA rows are `14.49 1.38 15.87 5.55` and `0.63 0.29 0.92 5.54`.
- `stage_rows.py` prints Table 4's rates, for example `TEMPA claude-sonnet-5 2970 99.83 99.83 41.18`.
- `figs_rq.py` redraws Figures 6–10 and B.3 into `paper/figures/` (it creates the directory).

Then build the mechanization:

```sh
cd mech && lake build && lake env lean Axioms.lean    # 2 min 12 s from scratch on our machine
```

`lake build` ends with `Build completed successfully (62 jobs).`, and each of the 29 lines that
`Axioms.lean` prints reads `depends on axioms: [propext, Classical.choice, Quot.sound]` or a subset of it.

## Step-by-Step Instructions

### Mode A: every number from the logs (no API key)

Run each command from the repository root. Each script writes its output next to itself;
`results/checks/README.md` describes every script, its inputs, and its runtime. Lines such as
`SyntaxWarning: invalid decimal literal` come from parsing student submissions and are expected.

| Paper | Command | Output and what to compare |
|---|---|---|
| Table 2, repair rates; Fig. 6; Sec. 4.2 counts | `python3 -I results/checks/rows/oos/a1_oos.py` | `rows/oos/A1_metrics.csv`, rows `subset=all`: `RR`, `RR_held`, `RR_0.25`, `RPS` per arm and model |
| Table 2, Median FL | `python3 -I results/checks/footprint/median_fl.py` (16 s) | `footprint/median_fl.txt`: 6; 5 and 6; 4 and 4 |
| Table 2, %Student | `python3 -I results/checks/student_fix/analyze.py .` | `student_fix/analyze.txt`: `precision` per tool, `chance on all 298: 59.0%` |
| App. B.2, the student's own fix | `python3 -I results/checks/student_fix/own_fix.py` | `student_fix/own_fix.txt`: precision where the own fix is not among the transplant's eight, 83.4% and 82.9%, and where the builder's pairs hold neither the program nor its fix, 81.5% and 83.8% |
| Sec. 3.2.2 and 4.2, footprints on CPython | `python3 -I results/checks/footprint/run.py .` (7 min), then `analyze.py .` | `footprint/summary.csv`: `inputs_checked` summed over Refactory, PyDex, rules, transplant, and fallback is 258,435; `violations` is 0 |
| Sec. 4.2, Expressiveness | `python3 -I results/checks/footprint/scope_rules.py` | `footprint/scope_rules.txt`: written 417, rejected 85 (for a scope: 0), scope rules 24 and 5, repairs 77 and 8, beyond the edited lines 2 and 0 |
| Table 3 | `python3 -I results/checks/rows/table3.py` | `rows/table3.txt` |
| Sec. 4.3, tokens generated | `python3 -I results/checks/rows/tokens.py` | `rows/tokens.txt`: 18.5 and 36.1 times fewer |
| Fig. 7, N\* and the ratio at 1,000 | `python3 -I results/checks/figures/figs_rq.py growth` | prints `N* 13.45, ratio at 1000 55.2` and `N* 6.09, ratio at 1000 61.6` |
| Table 4, Fig. 8 | `python3 -I results/checks/rows/stages/stage_rows.py`, then `figs_rq.py ablation` | `rows/stages/stage_rows.csv`; the figure's legend gives RR<sub>0.25</sub> |
| Fig. 9 | `python3 -I results/checks/figures/figs_rq.py rq4` | `paper/figures/fig_rq4_a.pdf`, from `results/sensitivity.csv` |
| Fig. 10 | `python3 -I results/checks/rows/rule_traits/recurring.py`, then `figs_rq.py rules_compact` | `rows/rule_traits/recurring.json` |
| Sec. 4.5, rules written, passing, used | `python3 -I results/checks/rows/rule_traits/rules_used.py` | `rows/rule_traits/rules_used.txt`: 191, 188, 150 and 226, 144, 71 |
| App. A.2, rejected rules | `python3 -I results/checks/footprint/static_off.py .`, then `static_off_run.py .` | `footprint/static_off.txt`, `static_off_run.txt` |
| App. A.3, mechanization against CPython (after mode B's build) | `results/checks/lean_sem/difftest.py .`, `coretest.py .`, `results/checks/lean_cls/surf_cls.py .` | `difftest.txt`, `coretest.txt`, `surf_cls.txt` |
| App. A.5, the bound and the draws | `results/checks/oracle_theory/vote_margin.py`, `certified.py`, `results/checks/iid/replay.py` | `vote_margin.txt`, `certified.txt`, `replay.txt` |
| App. B.1, the held-out suites | `python3 -I results/checks/cf_heldout/cf_heldout.py all` | `cf_heldout/shares.csv` |
| App. B.1, Refactory's unrepaired programs (after `a1_oos.py`) | `python3 -I results/checks/rows/oos/refactory_split.py` | `rows/oos/refactory_split.txt`: 495 = 254 on C1–C6 + 241 on R1–R5 (166 with no repair passing T) |
| App. B.2, equal oracles | `python3 -I results/checks/rows/oos/a4_equal_oracle.py` | `rows/oos/A4_metrics.csv` |
| App. B.3, Fig. B.2 | `python3 -I results/checks/rows/oos/a3_frontier.py` | `rows/oos/A3_points.csv`, `A3_frontier.csv`, `fig_pareto.pdf` |
| App. B.4, rules as Python functions, Fig. B.3 | `results/checks/python_rules/compare.py .`, `rule_size.py .`, `audit.py .` | `compare.txt`, `rule_size.txt`, `audit.txt` |
| App. B.4, three builds | `python3 -I results/checks/rows/oos/a2_rebuild_rules.py` | `rows/oos/A2_metrics.csv`, `A2_range.csv` |
| App. B.4, three builds, the bootstrap interval | `python3 -I results/checks/rows/stages/gap_bootstrap.py` | `rows/stages/gap_bootstrap.txt`: `Delta 8.7 [7.4, 10.0]` |
| App. B.4, gain per assignment, Table B.2 | `python3 -I results/checks/baselines/analyze.py`, then `rules_where.py` | `baselines/rules_where.txt` |

The scripts of `rows/` depend on one another; run them in the order of `results/checks/README.md`.
`a1_oos.py` and `a2_gate.py` read the held-out verdicts from `cache/` when it is present and
otherwise run the held-out suites again.

### Mode B: the mechanization

`mech/` proves the footprint theorem for PyCore (`PyCore.footprint_theorem`, through the
lock-step simulation `PyCore.step_sim`) and for Python programs through the translation
(`Surf.translation_keeps_scopes`, `Surf.tr_edit`, `Surf.footprint_theorem_surf`), with no `sorry`,
`admit`, or `axiom` declaration. `mech/NOTES.md` states each theorem in Lean and maps it to the paper.

| Paper | Lean |
|---|---|
| Theorem 5 (Footprint), for PyCore | `PyCore.footprint_theorem` |
| Lemma A.2 (Step) | `PyCore.step_sim` |
| Lemma A.3 (Translation) | `Surf.translation_keeps_scopes`, `Surf.tr_edit`, `Surf.T2.t2`, `Surf.T2.reach_corr` |
| Theorem 5 for Python runs | `Surf.T2.footprint_theorem_surf_sem` |

```sh
cd mech && lake build                      # every default target
lake env lean Axioms.lean                  # 29 declarations
lake env lean AxiomsT2.lean                # 52 declarations
```

### Mode C: rerunning with a model (API keys and cost)

These commands rebuild tools and call the models; their exact output differs from the logged
run, because the models' answers vary. The logged build cost is $14.49 with `claude-sonnet-5`
and $0.63 with `gpt-5.4-mini` for all 11 assignments (Table 3); one assignment costs $0.20 to
$2.16 and $0.01 to $0.16 (Table B.4).

```sh
python run.py build   --problem <pid> --model <model>                 # build a tool
python run.py augment amplify --model <model> --regenerate            # a new generator, then T+
python run.py compare --problem <pid> --model <model> --amplified     # TEMPA and TEMPA^-fallback
python run.py direct  --problem <pid> --model <model> --amplified     # the fallback API call for every program
python run.py pydex   --problem <pid> --model <model>                 # PyDex
```

A built tool runs without a model:

```sh
python run.py compare --problem refactory_q1 --model claude-sonnet-5 --amplified --no-llm --ver rerun
```

The rule search and the tests run under wall-clock limits (3 s per search, 2 s per test), so
run on an otherwise idle machine.

## Claims Supported

- Every number in Section 4 and Appendix B is recomputed exactly from the logged rows by
  mode A, without a model call.
- The footprint theorem and its translation to Python runs are checked by Lean (mode B), and
  the CPython checks of Section 3.2.2 and Appendix A.3 rerun from the logged programs.

## Claims Not Supported

- Mode C does not reproduce the logged numbers exactly: a new build writes other rules, and a
  new API call returns other answers. Appendix B.4's three builds show how much a rebuild moves.
- The times of Table 3 (ATT) are the logged times of the runs and the providers' APIs; mode A
  recomputes them from the logs, but a rerun takes other times, so compare the order of the
  tools rather than the seconds.
- Refactory's code is not included; the logs keep its results. `results/checks/rows/refactory_oracle.py`
  and a rerun of Refactory expect its released code in `baselines/refactory/`. Rerunning Refazer needs Mono and
  takes hours (`results/checks/baselines/compare_with.py`).
- `results/checks/student_fix/fetch.py` reads Codeforces' public API; the repository keeps its
  output, with an integer in place of each handle.

## Data

- R1–R5: the introductory programming corpus released with Refactory.
- C1–C6: Codeforces submissions mirrored by the open-r1 release.

Each corpus keeps its own buggy and correct labels.
