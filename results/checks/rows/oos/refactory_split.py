"""Where Refactory's unrepaired programs lie (Appendix B.1).

Splits the programs without a held-out-passing Refactory repair (A1_rows.csv) into C1-C6, where
the held-out suite is T, and R1-R5, by whether a repair passes T. Logs only.
    python3 -I results/checks/rows/oos/refactory_split.py"""
from pathlib import Path
import pandas as pd

HERE = Path(__file__).parent
d = pd.read_csv(HERE / "A1_rows.csv", dtype={"buggy": str})
d = d[(d.arm == "Refactory") & (d.model == "claude-sonnet-5")]   # Refactory uses no model; one copy
assert len(d) == 2970
fixed, held = d.fixed.astype(str) == "True", d.held.astype(str) == "True"
r = d.pid.str.startswith("refactory_")
out = [f"unrepaired (no repair passing T and the held-out suite): {(~held).sum()}",
       f"  C1-C6 (held-out suite = T): {(~held & ~r).sum()}",
       f"  R1-R5: {(~held & r).sum()}  (no repair passing T: {(~fixed & r).sum()}, passes T but fails held-out: {(fixed & ~held & r).sum()})"]
(HERE / "refactory_split.txt").write_text("\n".join(out) + "\n")
print("\n".join(out))
