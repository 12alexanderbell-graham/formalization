import sys; sys.path.insert(0, "/home/claude/t5AS")
from common import *
R = root()
row = ("| C33 | Capozziello, Lazkoz, Salzano 2011 (arXiv:1104.3096), Eq. (22); Capozziello, Cardone, Salzano 2008 Eq. (40) | CPL l₀ w_a² term, factor 9 | "
       "WITHDRAWN: the referee's convention check (sign of k and the w_a time variable) shows the printed term is right in the paper's own variables; the earlier Lean finding on it was retracted and its blocks are obsolete, do not cite them |\n")
edit(R, LAST, LAST + row)
ledger(R, "- Run 2026-11-15T1028Z: FINDINGS.md candidates table, new row C33 (status note on the CPL l₀ entry); verified section untouched.")
regen(R)
