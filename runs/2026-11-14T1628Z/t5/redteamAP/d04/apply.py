import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)) + '/..')
from common import *
root = sys.argv[1]
t = load(root)
MARK = '- **Unchecked notes** (author prose under rule FB10 of `scripts/trust/check_findings.py`: no check reads what these lines claim; the first of them is the author\'s title; trust only the generated heading, the generated lines and the certified block above):\n'

sec = section(t, "F8")
add = ("  Correct, checked against Lean (`F8_sizes`): at z = 1 the omitted z⁵ term is 56 per cent of the retained series and at z = 2 it is 670 per cent\n"
       "  -\n")
new = sec.rstrip("\n") + "\n\n" + add
new = new + sec[len(sec.rstrip("\n")) + 1:]
t = t.replace(sec, new, 1)
save(root, t)
ledger(root, "F8", "checked-size line added to the notes of the finding")
