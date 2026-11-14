import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)) + '/..')
from common import *
root = sys.argv[1]
t = load(root)

row = "| C32 | Planck 2018 results VI (arXiv:1807.06209) Table 2, Ω_m column | printed Ω_m = 0.3153 should be 0.3053 (digit slip) | → **F1** (run 1628Z) |\n"
anchor = "| C3 | Capozziello, Cardone, Salzano 2008 | — | → **F3** |\n"
assert anchor in t
t = t.replace(anchor, anchor + row, 1)
save(root, t)
ledger(root, "F1", "candidate index row added")
