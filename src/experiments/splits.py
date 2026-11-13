"""`run.py splits` — build on earlier submissions, repair later ones.

Here a tool and its reference pool see only a training prefix of the
submissions, and it is scored on later buggy programs it could not have seen:

* Codeforces (C1-C5): a temporal split. Submission ids are assigned in time
  order, so the last quarter of all submissions (buggy and correct) is the
  future; its buggy programs are the test set.
* CS1 (R1-R5): the corpus records neither student nor time, so the order is a
  seeded shuffle (seeds 0-2) and the same positional split applies.

The training pool is the first 10% of that order, and the test set is the
last quarter. C6 has five submissions and is left out. "same" repairs the test set with the tools of
the main evaluation (tools/), as a reference measured under the same load.

On R1-R5 the tool accepts against T+ as in the main evaluation. The builder's
generator sees no submission, so it is the one in benchmark/; only the labels
change, since the voters are the training pool's correct programs -- the ones a
course would hold at that point.

    python run.py splits make                 # splits_work/: the splits and their suites
    python run.py splits jobs --phase build   # one line per missing tool -> tools/splits/
    python run.py splits jobs --phase eval    # one line per (scheme, f|same, pid)
    python run.py splits report               # -> results/splits/report.csv

splits_work/ is regenerated deterministically and not tracked; evaluation runs
on copies of the tools there, so a run never touches tools/.
"""
from __future__ import annotations

import argparse
import json
import random
import shutil
from pathlib import Path

import pandas as pd

ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / "benchmark"
SPLITS = ROOT / "splits_work"
TOOLS = ROOT / "tools" / "splits"
RESULTS = ROOT / "results" / "splits"

CS1 = ["refactory_q1", "refactory_q2", "refactory_q3", "refactory_q4", "refactory_q5"]
CF = ["cf_110A", "cf_131A", "cf_1011B", "cf_125A", "cf_11B"]
FRACS = [10]
TEST = 0.25
SCHEMES = {"s0": 0, "s1": 1, "s2": 2}        # CS1 shuffle seeds; CF is temporal (s0)
MODELS = ["claude-sonnet-5", "gpt-5.4-mini"]


def _order(pid: str, seed: int) -> list[tuple[str, str]]:
    """All submissions as (kind, stem) in the split order."""
    subs = [(k, p.stem) for k in ("buggy", "correct")
            for p in sorted((DATA / pid / k).glob("*.py"))]
    if pid in CF:
        return sorted(subs, key=lambda s: int(s[1]))
    random.Random(seed).shuffle(subs)
    return subs


def schemes_for(pid: str) -> list[str]:
    return ["s0"] if pid in CF else list(SCHEMES)


def _amplify(scheme: str, tag: str, pid: str) -> None:
    """eval_amplified/<model>/<pid>/: the eval dir with T+ labelled by its pool."""
    from src.experiments.augment import amplified_tests
    src = SPLITS / scheme / tag / "eval" / pid
    prob = json.loads((src / "problem.json").read_text())
    for m in MODELS:
        code = (DATA / pid / "amplified" / m / "generator.py").read_text()
        d = SPLITS / scheme / tag / "eval_amplified" / m / pid
        shutil.rmtree(d, ignore_errors=True)
        shutil.copytree(src, d)
        kept = amplified_tests(pid, code, src / "correct")
        (d / "problem.json").write_text(json.dumps(dict(prob, tests=prob["tests"] + kept,
                                                           n_instructor=len(prob["tests"])), indent=1))


def make() -> dict:
    manifest = {}
    for pid in CS1 + CF:
        for scheme in schemes_for(pid):
            order = _order(pid, SCHEMES[scheme])
            cut = int(round(len(order) * (1 - TEST)))
            test = [s for k, s in order[cut:] if k == "buggy"]
            entry = {"test": test, "train": {}}
            for f in FRACS:
                head = order[:int(round(len(order) * f / 100))]
                tb = [s for k, s in head if k == "buggy"]
                tc = [s for k, s in head if k == "correct"]
                entry["train"][f] = {"buggy": tb, "correct": tc}
                base = SPLITS / scheme / f"f{f:02d}"
                for part, buggy, correct in (("train", tb, tc), ("eval", test, tc)):
                    d = base / part / pid
                    shutil.rmtree(d, ignore_errors=True)
                    for kind, stems in (("buggy", buggy), ("correct", correct)):
                        (d / kind).mkdir(parents=True)
                        for s in stems:
                            shutil.copy(DATA / pid / kind / f"{s}.py", d / kind / f"{s}.py")
                    shutil.copy(DATA / pid / "problem.json", d / "problem.json")
            # same test programs, the full pool and the campaign's own tools: the
            # same-pool reference, re-measured under the same machine load
            d = SPLITS / scheme / "same" / "eval" / pid
            shutil.rmtree(d, ignore_errors=True)
            (d / "buggy").mkdir(parents=True)
            shutil.copytree(DATA / pid / "correct", d / "correct")
            for s in test:
                shutil.copy(DATA / pid / "buggy" / f"{s}.py", d / "buggy" / f"{s}.py")
            shutil.copy(DATA / pid / "problem.json", d / "problem.json")
            if pid in CS1:
                for tag in [f"f{f:02d}" for f in FRACS] + ["same"]:
                    _amplify(scheme, tag, pid)
            manifest.setdefault(scheme, {})[pid] = entry
            print(f"{scheme} {pid}: test {len(test)} buggy; train "
                  + ", ".join(f"{f}%={len(entry['train'][f]['buggy'])}b/"
                              f"{len(entry['train'][f]['correct'])}c" for f in FRACS))
    (SPLITS / "manifest.json").write_text(json.dumps(manifest, indent=1))
    return manifest


def jobs(models: list[str] = MODELS, phase: str = "build") -> None:
    """Shell lines, one per job.

    build: one line per (scheme, f, pid, model), skipped when that tool exists;
           LLM-bound, so it tolerates a busy machine.
    eval:  one line per (scheme, f|same, pid) running every compare for it in
           sequence (they share one results file). The rule search and the
           tests run under wall clocks, so this phase should run on a quiet
           machine.
    """
    work = SPLITS / "tools"
    if phase == "eval" and not work.exists():
        skip = shutil.ignore_patterns("__pycache__")
        shutil.copytree(TOOLS, work, ignore=skip)
        shutil.copytree(ROOT / "tools", work / "same", ignore=shutil.ignore_patterns(
            "__pycache__", "splits"))
    for scheme in SCHEMES:                     # s0 first, so results land early
        for f in FRACS + (["same"] if phase == "eval" else []):
            tag = f if f == "same" else f"f{f:02d}"
            for pid in CS1 + CF:
                if scheme not in schemes_for(pid):
                    continue
                base = SPLITS.relative_to(ROOT) / scheme / tag
                if phase == "build":
                    for m in models:
                        if (TOOLS / scheme / tag / pid / m / "cost.json").exists():
                            continue
                        print(f"python3 run.py build --problem {pid} --data-root {base}/train "
                              f"--tools-root tools/splits/{scheme}/{tag} --model {m}")
                    continue
                tools = work.relative_to(ROOT) / ("same" if f == "same" else f"{scheme}/{tag}")
                ev = ((lambda m: f"{base}/eval_amplified/{m}") if pid in CS1
                      else (lambda m: f"{base}/eval"))
                ver = f"splits/{scheme}/{tag}"
                cmds = [f"python3 run.py compare --problem {pid} --data-root {ev(m)} "
                        f"--tools-root {tools} --ver {ver} --model {m}" for m in models]
                cmds += [f"python3 run.py compare --problem {pid} --data-root {ev(models[0])} "
                         f"--tools-root {tools} --ver {ver} --model {models[0]} --framework-only"]
                print(" && ".join(cmds))


def _arm(ver: Path, pid: str, stem: str, model: str) -> tuple[int, int, float]:
    f = ver / pid / f"{stem}.csv"
    if not f.exists():
        return 0, 0, 0.0
    d = pd.read_csv(f, keep_default_na=False)
    d = d[d.Model.astype(str) == model]
    ok = d[d.Fixed.astype(str) == "True"]
    return len(d), len(ok), float(pd.to_numeric(ok.RPS).sum())


def report(models: list[str] = MODELS) -> pd.DataFrame:
    """results/splits/report.csv: one row per (scheme, f, pid, model)."""
    manifest = json.loads((SPLITS / "manifest.json").read_text())
    rows = []
    for scheme, pids in manifest.items():
        for pid, entry in pids.items():
            for f in FRACS:
                ver = RESULTS / scheme / f"f{f:02d}"
                for model in models:
                    cost = TOOLS / scheme / f"f{f:02d}" / pid / model / "cost.json"
                    c = json.loads(cost.read_text()) if cost.exists() else {}
                    row = {"scheme": scheme, "f": f, "pid": pid, "model": model,
                           "n_test": len(entry["test"]),
                           "train_buggy": len(entry["train"][str(f)]["buggy"]),
                           "train_correct": len(entry["train"][str(f)]["correct"]),
                           "pairs": c.get("n_samples"), "in_tok": c.get("in_tokens"),
                           "out_tok": c.get("out_tokens"), "build_usd": c.get("usd"),
                           "build_s": c.get("build_seconds")}
                    for arm, stem, m in (("L", "tempa_l", model), ("LF", "tempa_lf", model),
                                         ("fw", "tempa_l_fw", models[0])):
                        n, k, rps = _arm(ver, pid, stem, m)
                        row[f"{arm}_n"], row[f"{arm}_fixed"], row[f"{arm}_rps_sum"] = n, k, rps
                    for arm, stem in (("same_L", "tempa_l"), ("same_LF", "tempa_lf")):
                        n, k, rps = _arm(RESULTS / scheme / "same", pid, stem, model)
                        row[f"{arm}_n"], row[f"{arm}_fixed"], row[f"{arm}_rps_sum"] = n, k, rps
                    rows.append(row)
    df = pd.DataFrame(rows)
    out = RESULTS / "report.csv"
    out.parent.mkdir(parents=True, exist_ok=True)
    df.to_csv(out, index=False)
    print(f"-> {out}")
    return df


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(prog="run.py splits")
    ap.add_argument("action", choices=["make", "jobs", "report"])
    ap.add_argument("--models", nargs="+", default=MODELS)
    ap.add_argument("--phase", choices=["build", "eval"], default="build")
    args = ap.parse_args(argv)
    if args.action == "make":
        make()
    elif args.action == "jobs":
        jobs(args.models, args.phase)
    else:
        report(args.models)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
