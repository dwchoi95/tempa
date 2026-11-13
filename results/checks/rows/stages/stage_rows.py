"""Per-program rows of TEMPA and its stage ablations, for RQ3's table and figure.

    TEMPA       the full tool (A1 TEMPA_LF)
    rand        Select replaced by random pairs (tools/select_rand, results/select_rand)
    built-in    Build's rules removed, built-in rules kept (A1 -rules)
    Refazer     Build's rules replaced by Refazer's (checks/baselines rows.csv)
    -amp        accepting against T alone (A1 -amp)
    -transplant Repair without the transplant: the rules, then the fallback,
                composed from the logged runs as compose.py composes TEMPA
    -fallback   Repair without the fallback API call (A1 TEMPA_L)
    Python      Build's rules written as Python functions (python_rows.py)
    line, block the transplant adopting only line hunks, or only whole top-level
                statements (A1 line only, block only)

No model call. Writes stage_rows.csv next to itself.
    python3 -I results/checks/rows/stages/stage_rows.py"""
import sys
from pathlib import Path
import pandas as pd

ROOT = Path(__file__).resolve().parents[4]
OUT = Path(__file__).with_name("stage_rows.csv")
GATE = 1.0                                              # compose.RPS_GATE
COLS = ["arm", "pid", "model", "buggy", "fixed", "held", "rps"]


def _b(s):
    return s.astype(str) == "True"


def load():
    a1 = pd.read_csv(ROOT / "results/checks/rows/oos/A1_rows.csv", keep_default_na=False)
    a1["fixed"], a1["held"] = _b(a1.fixed), _b(a1.held)
    a1["rps"] = pd.to_numeric(a1.rps, errors="coerce")
    bl = pd.read_csv(ROOT / "results/checks/baselines/rows.csv", keep_default_na=False)
    bl = bl[bl.arm == "refazer | +fallback"].copy()
    bl["fixed"], bl["held"] = _b(bl.fixed), _b(bl.held)
    bl["rps"] = pd.to_numeric(bl.rps, errors="coerce")
    return a1, bl


def no_transplant(a1):
    """Rules first; whatever they leave, or repair with RPS > GATE, goes to the
    logged fallback answer, the smaller passing patch kept (compose.compose)."""
    lo = a1[a1.arm == "TEMPA_L"].set_index(["pid", "model", "buggy"])
    fb = a1[a1.arm == "LLM_Direct"].set_index(["pid", "model", "buggy"])
    src = []
    for pid in lo.index.get_level_values(0).unique():
        c = pd.read_csv(ROOT / "results" / pid / "tempa_l.csv", keep_default_na=False)
        src.append(pd.DataFrame({"pid": pid, "model": c.Model, "buggy": c.Buggy.astype(str), "source": c.Source}))
    src = pd.concat(src).set_index(["pid", "model", "buggy"]).source
    rows = []
    for k, l in lo.iterrows():
        rules_ok = bool(l.fixed) and src[k] == "rules"
        if rules_ok and l.rps <= GATE:
            keep = l
        else:
            f = fb.loc[k]
            keep = f if (f.fixed and (not rules_ok or f.rps < l.rps)) else (l if rules_ok else f)
        rows.append({"arm": "-transplant", "pid": k[0], "model": k[1], "buggy": k[2],
                     "fixed": bool(keep.fixed), "held": bool(keep.held), "rps": keep.rps if keep.fixed else None})
    return pd.DataFrame(rows)


def rand_rows():
    p = ROOT / "results/checks/rows/stages/rand_rows.csv"   # select_report.py
    if not p.exists():
        return pd.DataFrame(columns=COLS)
    d = pd.read_csv(p, keep_default_na=False)
    d["fixed"], d["held"] = _b(d.fixed), _b(d.held)
    d["rps"] = pd.to_numeric(d.rps, errors="coerce")
    return d[COLS]


def python_rows():
    d = pd.read_csv(Path(__file__).with_name("python_rows.csv"), keep_default_na=False)
    d = d[d.arm == "Python"].copy()
    d["fixed"], d["held"] = _b(d.fixed), _b(d.held)
    d["rps"] = pd.to_numeric(d.rps, errors="coerce")
    return d[COLS]


if __name__ == "__main__":
    a1, bl = load()
    name = {"TEMPA_LF": "TEMPA", "-rules": "built-in", "-amp": "-amp", "TEMPA_L": "-fallback",
            "line only": "line", "block only": "block"}
    parts = [a1[a1.arm.isin(name)].assign(arm=lambda d: d.arm.map(name))[COLS],
             rand_rows(), bl.assign(arm="Refazer")[COLS], no_transplant(a1), python_rows()]
    d = pd.concat(parts, ignore_index=True)
    d["buggy"] = d.buggy.astype(str)
    d.to_csv(OUT, index=False)
    d["s"] = d.fixed & d.held & (d.rps <= 0.25)
    g = d.groupby(["arm", "model"])
    t = pd.DataFrame({"n": g.size(), "RR_T": 100 * g.fixed.mean(), "RR_H": 100 * g.held.mean(),
                      "RR_0.25": 100 * g.s.mean()})
    print(t.round(2).to_string())
    print(t.groupby("arm").mean().round(2).to_string())
