"""TEMPA^Python: TEMPA with the main build's rules written as Python functions.

Reads the frozen run of the Python tools (lang_vs_python/run/r0/<pid>/tempa_l.csv, no model),
composes the fallback from the campaign's logged answers as compose.py composes TEMPA, and
judges R1-R5 on T plus the held-out suite with A1's cached judge (held = repaired on C1-C6).
Writes python_rows.csv next to itself. No model call.
    python3 -I results/checks/rows/stages/python_rows.py"""
import importlib.util
import sys
from pathlib import Path
import pandas as pd

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT))
from src.experiments._common import ORDER                   # noqa: E402
from src.experiments.compose import compose                 # noqa: E402
from src.experiments.results_io import read_events          # noqa: E402

spec = importlib.util.spec_from_file_location("a1", ROOT / "results/checks/rows/oos/a1_oos.py")
a1 = importlib.util.module_from_spec(spec); spec.loader.exec_module(a1)
RUN = ROOT / "results/checks/python_rules/run/r0"
MODELS, CS1 = ["claude-sonnet-5", "gpt-5.4-mini"], ORDER[:5]

rows = []
for pid in ORDER:
    loc = pd.read_csv(RUN / pid / "tempa_l.csv", keep_default_na=False)
    for m in MODELS:
        local = [dict(r, Fixed=r["Fixed"] in (True, "True"), RPS=float(r["RPS"]) if r["RPS"] not in ("", "None") else None,
                      Buggy=str(r["Buggy"])) for r in loc[loc.Model == m].to_dict("records")]
        lf = compose(local, read_events("", pid, "direct_llm", m))
        for arm, xs in (("Python", lf), ("Python -fallback", local)):
            h = a1.held(pid, {x["Patch"] for x in xs if x["Fixed"]}) if pid in CS1 else {}
            for x in xs:
                ok = bool(x["Fixed"])
                rows.append({"arm": arm, "pid": pid, "model": m, "buggy": str(x["Buggy"]), "fixed": ok,
                             "held": ok and (h[a1.sha(x["Patch"])] if pid in CS1 else True),
                             "rps": x["RPS"] if ok else None, "source": x["Source"]})
d = pd.DataFrame(rows)
d.to_csv(Path(__file__).with_name("python_rows.csv"), index=False)
d["s"] = d.held & (pd.to_numeric(d.rps) <= 0.25)
g = d.groupby(["arm", "model"])
print(pd.DataFrame({"n": g.size(), "RR_T": 100 * g.fixed.mean(), "RR_H": 100 * g.held.mean(),
                    "RR_0.25": 100 * g.s.mean(), "small": g.s.sum()}).round(2).to_string())
