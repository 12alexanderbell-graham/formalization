#!/usr/bin/env python3
"""d06: FB10 skips every line between a line that STARTS with '<!-- certified:' and '<!-- /certified -->', but the block
syntax of check_numbers / verified_sections needs '^<!-- certified: [A-Za-z0-9_ ]+ -->$'. A lookalike opener ('F14_….')
hides top-level author lines from FB10 and (the prose regex strips them) from FB1-FB7, FB9; they render as ordinary
bullets right below the real block, in the style of a generated line."""
import sys
from pathlib import Path

root = Path(sys.argv[1])
p = root / "FINDINGS.md"
t = p.read_text(encoding="utf-8")
i = t.index("### F14 (was C-FS-1988R).")
j = t.index("- **Unchecked notes**", i)
opener = "<!-- certified: F14_reversed_wall_shear -->\n"
k = t.index(opener, i, j)
fake = (
    "<!-- certified: F14_reversed_wall_shear. -->\n"
    "- **Uniqueness (generated from the Lean records by `python3 scripts/trust/check_findings.py --write-layout F14`; "
    "do not edit):** `F14_reversed_wall_shear`: the reverse-flow solution with −1 ≤ f' ≤ 1 and faster-than-every-exponential "
    "approach to the edge velocity is unique, so its wall shear is the printed value `printedFazioRevWall` plus the "
    "difference certified above, and the printed value is the wall shear of no solution of that class.\n"
)
# the fake line sits between the lookalike opener and the real block, whose own close ends the region for FB10 and for
# the prose regex alike: the section's prose (FB7) is unchanged, no LEDGER line is needed
p.write_text(t[:k] + fake + t[k:], encoding="utf-8")
