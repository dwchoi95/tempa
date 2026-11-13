"""Footprint pruning in the evaluated search (Corollary 3.14), against the same search
without it: for every buggy program of one assignment and builder, run the frozen tool's
rule search twice, back to back on the same machine, and record the outcome, the
candidates validated and pruned, and the wall time. Resumable: programs already in
rows/<pid>__<model>.csv are skipped. No model call.
    python3 results/checks/prune/run.py PID MODEL"""
import csv, signal, sys, time
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]; sys.path.insert(0, str(ROOT))
from src.experiments._common import load_problem, tool_path   # noqa: E402
from src.core.synthesis import load_fixer                      # noqa: E402
from src.core.repair import repair, SearchBudget               # noqa: E402

LIMIT = 1800                                                   # seconds, pruned arm only


class Overrun(Exception):
    pass


def _overrun(*_):
    raise Overrun


signal.signal(signal.SIGALRM, _overrun)
pid, model = sys.argv[1], sys.argv[2]
out = Path(__file__).with_name("rows") / f"{pid}__{model}.csv"
done = {r["buggy"] for r in csv.DictReader(open(out))} if out.exists() else set()
prob = load_problem(pid, str(ROOT / "benchmark"), model)
rules = load_fixer(ROOT / tool_path(pid, model))
cols = ["pid", "model", "buggy"] + [f"{a}_{k}" for a in ("off", "on") for k in
                                    ("repaired", "tried", "pruned", "cut", "seconds", "rules", "patch")]
new = not out.exists()
with open(out, "a", newline="") as fh:
    w = csv.DictWriter(fh, cols)
    if new:
        w.writeheader()
    for f in sorted((ROOT / "benchmark" / pid / "buggy").glob("*.py")):
        if f.stem in done:
            continue
        src, row = f.read_text(), {"pid": pid, "model": model, "buggy": f.stem}
        for arm, prune in (("off", False), ("on", True)):
            t0 = time.time()
            # Unvalidated candidates still seed deeper layers, so a pruned search can
            # run long on candidates that keep growing; stop it at LIMIT and record that.
            signal.alarm(LIMIT if prune else 0)
            try:
                r = repair(src, prob, rules, SearchBudget(prune=prune))
            except Overrun:
                row.update({f"{arm}_repaired": False, f"{arm}_tried": "", f"{arm}_pruned": "",
                            f"{arm}_cut": "timeout", f"{arm}_seconds": LIMIT,
                            f"{arm}_rules": "", f"{arm}_patch": ""})
                continue
            finally:
                signal.alarm(0)
            row.update({f"{arm}_repaired": r.repaired, f"{arm}_tried": r.candidates_tried,
                        f"{arm}_pruned": r.pruned, f"{arm}_cut": r.cut,
                        f"{arm}_seconds": round(time.time() - t0, 3),
                        f"{arm}_rules": "|".join(r.rules), f"{arm}_patch": r.patch or ""})
        w.writerow(row); fh.flush()
print(pid, model, "done")
