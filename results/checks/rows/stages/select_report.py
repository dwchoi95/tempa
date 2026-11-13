"""TEMPA^rand: TEMPA_LF with the random-selection rules, composed and judged as A1 judges TEMPA.

Reads results/select_rand/<model>/<pid>/tempa_l.csv (run_eval.sh), composes the
fallback from the campaign's logged answers (compose.compose, as for TEMPA),
writes tempa_lf.csv beside it, and judges the repairs of R1-R5 on T plus the
held-out suite with A1's cached judge (held = repaired on C1-C6). Checks first
that composing the campaign's own TEMPA_L reproduces A1's TEMPA rows.
Writes results/checks/rows/stages/rand_rows.csv. No model call.

    python3 -I results/checks/rows/stages/select_report.py"""
import importlib.util
import json
import sys
from pathlib import Path

import pandas as pd

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT))
from src.experiments._common import ORDER                       # noqa: E402
from src.experiments.compose import compose                      # noqa: E402
from src.experiments.results_io import read_events, write_events  # noqa: E402

spec = importlib.util.spec_from_file_location("a1", ROOT / "results/checks/rows/oos/a1_oos.py")
a1 = importlib.util.module_from_spec(spec); spec.loader.exec_module(a1)
MODELS, CS1 = ["claude-sonnet-5", "gpt-5.4-mini"], ORDER[:5]
OUT = ROOT / "results/checks/rows/stages/rand_rows.csv"


def sanity():
    ref = pd.read_csv(ROOT / "results/checks/rows/oos/A1_rows.csv", keep_default_na=False)
    ref = ref[ref.arm == "TEMPA_LF"]
    for m in MODELS:
        for pid in ORDER:
            lf = compose(read_events("", pid, "tempa_l", m), read_events("", pid, "direct_llm", m))
            got = {str(x["Buggy"]): bool(x["Fixed"]) for x in lf}
            want = {str(r.buggy): str(r.fixed) == "True" for r in ref[(ref.pid == pid) & (ref.model == m)].itertuples()}
            assert got == want, (pid, m, sum(got[k] != want.get(k) for k in got))
    print("sanity: composing the campaign's TEMPA_L reproduces A1's TEMPA rows")


def main():
    sanity()
    rows, cost = [], []
    for m in MODELS:
        for pid in ORDER:
            ver = f"select_rand/{m}"
            local = read_events(ver, pid, "tempa_l", m)
            assert local, (ver, pid)
            lf = compose(local, read_events("", pid, "direct_llm", m))
            write_events(ver, pid, "tempa_lf", lf)
            h = a1.held(pid, {x["Patch"] for x in lf if x["Fixed"]}) if pid in CS1 else {}
            for x in lf:
                ok = bool(x["Fixed"])
                rows.append({"arm": "rand", "pid": pid, "model": m, "buggy": str(x["Buggy"]), "fixed": ok,
                             "held": ok and (h[a1.sha(x["Patch"])] if pid in CS1 else True),
                             "rps": x["RPS"] if ok else None, "api_usd": x["$API"], "source": x["Source"]})
            c = json.loads((ROOT / "tools/select_rand" / pid / m / "cost.json").read_text())
            cost.append({"pid": pid, "model": m, "rules": c["rules"], "usd": c["usd"], "seconds": c["build_seconds"]})
    d = pd.DataFrame(rows); d.to_csv(OUT, index=False)
    c = pd.DataFrame(cost); c.to_csv(OUT.with_name("rand_cost.csv"), index=False)
    d["s"] = d.held & (pd.to_numeric(d.rps) <= 0.25)
    g = d.groupby("model")
    print(pd.DataFrame({"RR_T": 100 * g.fixed.mean(), "RR_H": 100 * g.held.mean(), "RR_0.25": 100 * g.s.mean(),
                        "rule repairs": g.apply(lambda x: (x.source == "rules").sum()),
                        "api_usd": g.api_usd.sum()}).round(2).to_string())
    print(c.groupby("model")[["rules", "usd", "seconds"]].sum().round(2).to_string())


if __name__ == "__main__":
    main()
