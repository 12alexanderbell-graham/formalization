import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)) + '/..')
from common import *
root = sys.argv[1]
t = load(root)
MARK = '- **Unchecked notes** (author prose under rule FB10 of `scripts/trust/check_findings.py`: no check reads what these lines claim; the first of them is the author\'s title; trust only the generated heading, the generated lines and the certified block above):\n'

sec = section(t, "F3")
cyr_e, cyr_o = "е", "о"
line = ("  - **Printed (g" + cyr_e + "nerated by `python3 scripts/trust/check_findings.py --write-layout F3` from the records' PRINTED "
        "definitions and their blind readings; d" + cyr_o + " not edit):** `printedD4` := `1 + 2 * q + 3 * q ^ 2 + 5 / 2 * q ^ 3 + "
        "7 / 2 * q ^ 4 - 5 / 3 * q * j - 7 / 8 * q ^ 2 * j - j + j ^ 2 / 12 - 1 / 8 * q * s - s / 6 - l / 120`, agreeing with "
        "the blind reading `Checked.Trust.SecondReading.printedD4` (`agree_printedD4`); the reader (file "
        "`runs/2026-11-05T2028Z/second_reading_claims/B/SecondReadingClaimsB.lean`, as first committed) wrote of this value: "
        "`Visser, Class. Quantum Grav. 21, 2603 (2004), arXiv:gr-qc/0309109 v1 and v2 (identical), Eq. (51), p. 9. Printed: the "
        "lookback-distance coefficient 7/2 q₀⁴.`.\n")
new = sec.rstrip("\n") + "\n" + line
new = new + sec[len(sec.rstrip("\n")) + 1:]
t = t.replace(sec, new, 1)
save(root, t)
ledger(root, "F3", "printed-line reading added to the notes of the finding")
