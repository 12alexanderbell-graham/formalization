import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)) + '/..')
from common import *
root = sys.argv[1]
t = load(root)
MARK = '- **Unchecked notes** (author prose under rule FB10 of `scripts/trust/check_findings.py`: no check reads what these lines claim; the first of them is the author\'s title; trust only the generated heading, the generated lines and the certified block above):\n'

sec = section(t, "F2")
assert MARK in sec
cont = ("  Reading note to this label (added with the F2 notes): of the notes below, the Scope statement that the "
        "printed l₀ is also correct whenever w₀ = −1 is confirmed by the certified record `F2_error`, so it is part of "
        "what this finding verifies.\n")
new = sec.replace(MARK, MARK + cont, 1)
t = t.replace(sec, new, 1)
save(root, t)
ledger(root, "F2", "reading note added to the notes of the finding")
