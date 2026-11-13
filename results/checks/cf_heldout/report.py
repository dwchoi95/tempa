"""Tables from rows.csv and cache/<pid>.json.

    python3 report.py   -> suite.csv, shares.csv, shares_by_problem.csv, rows_judged.csv, report.txt
"""
import json
from pathlib import Path

import pandas as pd

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
ORDER = ["refactory_q1", "refactory_q2", "refactory_q3", "refactory_q4", "refactory_q5",
         "cf_110A", "cf_131A", "cf_1011B", "cf_125A", "cf_11B", "cf_10C"]
CF = ORDER[5:]
IDS = {p: (f"R{i+1}" if i < 5 else f"C{i-4}") for i, p in enumerate(ORDER)}
MODELS = ["claude-sonnet-5", "gpt-5.4-mini"]
ARMS = ["TEMPA_LF", "TEMPA_L", "-rules", "-amp", "-rules-amp", "line only", "block only",
        "cluster-once", "gate 0.25", "gate 0.25 -rules", "LLM_Direct", "PyDex", "Refactory"]


def judged():
    """Each row's verdicts. Refactory's patches are judged in Refactory's own harness
    (the one its C1-C6 'fixed' comes from, cache/refactory_shim_*); the plain-harness
    verdict of its unwrapped patch (as R1-R5 run it) is kept as ind_plain/off_plain."""
    import hashlib
    d = pd.read_csv(HERE / "rows.csv", keep_default_na=False)
    d["buggy"] = d.buggy.astype(str)
    d["fixed"] = d.fixed.astype(str) == "True"
    d["rps"] = pd.to_numeric(d.rps, errors="coerce")
    v = {}
    for pid in CF:
        v.update(json.loads((HERE / "cache" / f"{pid}.json").read_text()))
        shim = json.loads((HERE / "cache" / f"refactory_shim_{pid}.json").read_text())
        v.update({"shim:" + h: x for h, x in shim.items()})
        r = pd.read_csv(ROOT / "results" / pid / "refactory.csv", keep_default_na=False)
        raw = {str(b): "shim:" + hashlib.sha1(str(p).encode()).hexdigest()
               for b, p, ok in zip(r.Buggy, r.Patch, r.Fixed.astype(str)) if ok == "True"}
        m = (d.pid == pid) & (d.arm == "Refactory") & d.fixed
        d.loc[m, "key"] = d.buggy[m].map(raw)
    plain = d.arm != "Refactory"
    d.loc[plain, "key"] = d.sha[plain]
    d["key"] = d.key.fillna("")
    missing = {h for h in d.key[d.fixed] if h not in v}
    assert not missing, f"{len(missing)} repaired texts not judged yet"
    d["ind"] = [bool(v[h]["ind"]) if ok else False for h, ok in zip(d.key, d.fixed)]
    d["off_recheck"] = [bool(v[h]["off"]) if ok else False for h, ok in zip(d.key, d.fixed)]
    d["ind_plain"] = [bool(v[h]["ind"]) if ok else False for h, ok in zip(d.sha, d.fixed)]
    d["off_plain"] = [bool(v[h]["off"]) if ok else False for h, ok in zip(d.sha, d.fixed)]
    return d, v


def main():
    d, v = judged()
    d.to_csv(HERE / "rows_judged.csv", index=False)
    pd.set_option("display.width", 250); pd.set_option("display.max_columns", 40)
    pd.set_option("display.max_rows", 500)
    out = []

    st = [json.loads((HERE / "suites" / f"stats_{p}.json").read_text()) for p in CF]
    st = pd.DataFrame([{k: s[k] for k in ("id", "pid", "drawn", "dup_official", "dup_earlier_draw",
                                          "candidates", "kept", "pool", "shown_to_builder", "voters",
                                          "need", "agree_mean_cands", "unanimous_cands",
                                          "agree_mean_kept", "agree_min_kept", "unanimous_kept",
                                          "voters_wrong_on_some_kept")}
                       | {"dropped": json.dumps(s["dropped"]), "classes_kept": json.dumps(s["classes_kept"])}
                       for s in st])
    st.to_csv(HERE / "suite.csv", index=False)
    out.append(st.to_string(index=False))

    rep = d[d.fixed]
    sh = rep.groupby(["arm", "model"]).agg(official=("ind", "size"), also_suite=("ind", "sum"),
                                           off_recheck_fail=("off_recheck", lambda s: int((~s).sum())),
                                           plain_off_fail=("off_plain", lambda s: int((~s).sum())),
                                           plain_also_suite=("ind_plain", "sum"))
    sh["share"] = 100 * sh.also_suite / sh.official
    sh["fail_suite"] = sh.official - sh.also_suite
    sh["distinct_fail_texts"] = rep[~rep.ind].groupby(["arm", "model"]).key.nunique()
    sh = sh.fillna({"distinct_fail_texts": 0}).reindex(
        pd.MultiIndex.from_product([ARMS, MODELS], names=["arm", "model"])).reset_index()
    sh.to_csv(HERE / "shares.csv", index=False)
    out.append(sh.round(2).to_string(index=False))
    sp = rep.groupby(["pid", "arm", "model"]).agg(official=("ind", "size"), also_suite=("ind", "sum")).reset_index()
    sp["id"] = sp.pid.map(IDS)
    sp.to_csv(HERE / "shares_by_problem.csv", index=False)
    piv = sp.assign(fail=sp.official - sp.also_suite).pivot_table(index=["arm", "model"], columns="id",
                                                                  values="fail", fill_value=0)
    out.append("failures (official-passing, suite-failing rows) by problem\n" + piv.to_string())

    txt = "\n\n".join(out)
    (HERE / "report.txt").write_text(txt + "\n")
    print(txt)


if __name__ == "__main__":
    main()
