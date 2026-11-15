import sys; sys.path.insert(0, "/home/claude/t5AS")
from common import *
R = root()
old = "- **Remaining:** promotion to Checked; CI; decide whether this is a finding or a parked misprint (it changes no reported number found so far)."
new = ("- **Remaining:** promotion to Checked is done: the Bonnor–Ebert threshold is verified finding F<!---->15 (record `Checked.Records.F<!---->15_critical`, "
       "Lean-certified 14.04 against the printed 13.98, blind second reading agrees); only the decision whether to report it outside the program is open.")
edit(R, old, new)
ledger(R, "- Run 2026-11-15T1028Z: FINDINGS.md candidate C-BE-1, Remaining line updated; no verified section touched.")
regen(R)
