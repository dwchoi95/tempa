"""The programs of the differential run: every buggy program and every distinct stored repair of
the arms tempa_l and tempa_lf, with their problem. python3 -I progs.py REPO -> counts."""
import csv, sys
from pathlib import Path
csv.field_size_limit(10**9)
ARMS = ("tempa_l", "tempa_lf")


def programs(REPO):
    """[(pid, kind, source)], kind 'buggy' or the arm; repairs deduplicated per (pid, arm, source)."""
    REPO = Path(REPO)
    out = []
    for pb in sorted((REPO / "benchmark").glob("*/problem.json")):
        pid = pb.parent.name
        for b in sorted((pb.parent / "buggy").glob("*.py")):
            out.append((pid, "buggy", b.read_text()))
        for arm in ARMS:
            f = REPO / "results" / pid / f"{arm}.csv"
            seen = set()
            if f.exists():
                for r in csv.DictReader(f.open()):
                    if r.get("Fixed") == "True" and r.get("Patch") and r["Patch"] not in seen:
                        seen.add(r["Patch"])
                        out.append((pid, arm, r["Patch"]))
    return out


if __name__ == "__main__":
    from collections import Counter
    print(Counter((p, k) for p, k, _ in programs(sys.argv[1])))
