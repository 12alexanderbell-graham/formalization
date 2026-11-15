import sys; sys.path.insert(0, "/home/claude/t5AS")
from common import *
R = root()
row = ("| C12b | Bamba et al. 2012 (11.18), (11.20); upstream Eqs. (20), (22) | the sign of the ḢṘ term (+ printed, − correct) | "
       "→ **F&#57;** (run 1428Z): second route done and certified in Lean by `printedR3Claim_false`; the P/Q formulas are refuted for every Ω |\n")
edit(R, LAST, LAST + row)
ledger(R, "- Run 2026-11-15T1028Z: FINDINGS.md candidates table, new row C12b (cross-reference only); no change to any `F9` section.")
regen(R)
