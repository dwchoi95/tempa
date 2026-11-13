"""What the candidates of static_off.py do: each runs on T+ beside its buggy program. A repair is a candidate that
passes T+, `new` one whose program no stored repair of the tool's main build reaches.
    python3 -I static_off_run.py REPO   -> static_off_run.txt"""
import csv, json, sys
from collections import Counter
from multiprocessing import Pool
from pathlib import Path
csv.field_size_limit(10**9)
REPO = Path(sys.argv[1]); sys.path.insert(0, str(REPO))
from src.experiments._common import load_problem    # noqa: E402
from src.runner.testing import run_tests            # noqa: E402
HERE = Path(__file__).resolve().parent


def job(r):
    p = load_problem(r["pid"], str(REPO / "benchmark"), r["model"])
    a = run_tests(r["patch"], p)
    f = dict(r, passes=a.all_pass, failed=len(a.signature()) if hasattr(a, "signature") else None,
             err=[x for x in (*a.signature(), a.error or "") if "NameError" in x or "UnboundLocal" in x][:2])
    return f


if __name__ == "__main__":
    rows = [json.loads(l) for l in (HERE / "static_off.jsonl").open()]
    with Pool(10) as p:
        res = p.map(job, rows, chunksize=4)
    done = {}
    for pid in {r["pid"] for r in rows}:
        for arm in ("tempa_lf",):
            f = REPO / "results" / pid / f"{arm}.csv"
            for x in csv.DictReader(f.open()):
                if x["Fixed"] == "True" and x["Patch"]:
                    done[pid, x["Buggy"], x["Model"]] = float(x["RPS"] or 9)
    c = Counter(); ex = []
    for r in res:
        k = r["why"]
        c[k, "candidates"] += 1
        c[k, "pass T+"] += r["passes"]
        c[k, "fail"] += not r["passes"]
        c[k, "fail with a name error"] += bool(r["err"]) and not r["passes"]
        if r["passes"]:
            c[k, "passing, program already repaired"] += (r["pid"], r["buggy"], r["model"]) in done
            if len(ex) < 6:
                ex.append((r["pid"], r["buggy"], r["model"], r["rule"]))
    txt = [f"{k}: {v}" for k, v in sorted(c.items(), key=str)] + [str(e) for e in ex]
    print("\n".join(txt)); (HERE / "static_off_run.txt").write_text("\n".join(txt) + "\n")
    with (HERE / "static_off_run.jsonl").open("w") as w:
        for r in res:
            w.write(json.dumps(r) + "\n")
