"""Appendix B.2, "The student's own fix": footprint precision on the programs whose own later fix the
transplant cannot adopt from. The transplant adopts from the eight correct programs nearest to a buggy
program (src/core/reference_repair.py, k_refs = 8); this script finds, for each of the 298 programs of
pairs.csv, whether the student's own fix is among them, and reports each tool's precision on the
programs where it is and where it is not, and on those where neither the buggy program nor its own fix is in
any of the builder's pairs (Select's pairs, src/core/synthesis.py) either. No model call.
    python3 -I results/checks/student_fix/own_fix.py   -> own_fix.txt   (after analyze.py)"""
import csv
import difflib
import statistics as st
import sys
from pathlib import Path

csv.field_size_limit(10**9)
ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))
from src.core.footprint import footprint_lines              # noqa: E402
from src.core.reference_repair import ReferenceIndex        # noqa: E402
from src.core.synthesis import select_sample_pairs          # noqa: E402
from src.experiments.build import load_pool                 # noqa: E402


def changed(b, c):
    """Lines of b (1-based) that the line diff from b to c touches, as in analyze.py."""
    x = [l.strip() for l in b.splitlines()]
    y = [l.strip() for l in c.splitlines()]
    out = set()
    for tag, i1, i2, _j1, _j2 in difflib.SequenceMatcher(None, x, y, autojunk=False).get_opcodes():
        if tag in ("replace", "delete"):
            out.update(range(i1 + 1, i2 + 1))
        elif tag == "insert":
            out.update(k for k in (i1, i1 + 1) if 1 <= k <= len(x))
    return out

HERE = Path(__file__).resolve().parent
ARMS = (("tempa_lf", "TEMPA"), ("pydex", "PyDex"), ("direct_llm", "LLM_Direct"), ("refactory", "Refactory"))
MODELS = ("claude-sonnet-5", "gpt-5.4-mini")
K_REFS = 8


def main():
    info, index, shown = {}, {}, {}
    for r in csv.DictReader((HERE / "pairs.csv").open()):
        pid = r["pid"]
        if pid not in index:
            index[pid] = ReferenceIndex([f.read_text() for f in sorted((ROOT / "benchmark" / pid / "correct").glob("*.py"))])
            pairs = select_sample_pairs(load_pool(pid, "buggy", str(ROOT / "benchmark")),
                                        load_pool(pid, "correct", str(ROOT / "benchmark")))
            shown[pid] = {b for b, _f, _n in pairs} | {f for _b, f, _n in pairs}
        b = (ROOT / "benchmark" / pid / "buggy" / f"{r['buggy']}.py").read_text()
        fix = (ROOT / "benchmark" / pid / "correct" / f"{r['fix']}.py").read_text()
        near = index[pid].nearest(b, K_REFS)
        info[(pid, r["buggy"])] = dict(src=b, ch=changed(b, fix), near=fix in near, first=bool(near) and near[0] == fix,
                                       unseen=fix not in near and b not in shown[pid] and fix not in shown[pid])
    out = [f"{len(info)} programs; own fix among the {K_REFS} nearest: {sum(v['near'] for v in info.values())} "
           f"(nearest: {sum(v['first'] for v in info.values())}); not among them: {sum(not v['near'] for v in info.values())}; "
           f"of these, in none of the builder's pairs either: {sum(v['unseen'] for v in info.values())}"]
    for arm, name in ARMS:
        for m in MODELS:
            if arm == "refactory" and m != MODELS[0]:
                continue
            prec = {True: [], False: []}; unseen = []
            for pid in sorted({k[0] for k in info}):
                for r in csv.DictReader((ROOT / "results" / pid / f"{arm}.csv").open()):
                    k = (pid, r["Buggy"])
                    if r["Model"] not in (m, "none") or k not in info or r["Fixed"] != "True" or not r["Patch"]:
                        continue
                    try:
                        F = footprint_lines(info[k]["src"], r["Patch"])
                    except SyntaxError:
                        continue
                    if F:
                        prec[info[k]["near"]].append(len(F & info[k]["ch"]) / len(F))
                        if info[k]["unseen"]:
                            unseen.append(len(F & info[k]["ch"]) / len(F))
            cell = lambda v: f"n {len(v)} precision {100 * st.mean(v):.1f}%" if v else "none"
            label = name if arm == "refactory" else f"{name} {m}"
            out.append(f"{label}: own fix among the {K_REFS}: {cell(prec[True])}; not: {cell(prec[False])}; "
                       f"not, and in no builder pair: {cell(unseen)}")
    text = "\n".join(out) + "\n"
    (HERE / "own_fix.txt").write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
