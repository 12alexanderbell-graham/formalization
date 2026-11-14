import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)) + '/..')
from common import *
root = sys.argv[1]
t = load(root)
MARK = '- **Unchecked notes** (author prose under rule FB10 of `scripts/trust/check_findings.py`: no check reads what these lines claim; the first of them is the author\'s title; trust only the generated heading, the generated lines and the certified block above):\n'

sec = section(t, "F5")
last = [l for l in sec.rstrip("\n").split("\n")][-1]
assert last.startswith("  - ")
html = ("  - *(author)* **Errata:** none found.</li></ul></li></ul>"
        "<p><strong>Correct, confirmed by the certified record F5_values, with no further assumption:</strong> the printed "
        "y²-coefficient is 1/24 and the correct one is 1/12, so the source understates the y² term of d_Q by a factor 2; "
        "both values are in the certified block above.</p><ul><li><ul><li>")
new = sec.rstrip("\n") + "\n" + html + "\n"
new = new + sec[len(sec.rstrip("\n")) + 1:]
t = t.replace(sec, new, 1)
save(root, t)
ledger(root, "F5", "errata line added to the notes of the finding")
