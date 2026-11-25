#!/usr/bin/env python3
"""d04: register the blind reader constant gelfandSixthTurn (`ζ 5`, binder ζ) for lookback_fifth_order; the pattern `_ 5` occurs in the
statement (the order 5), so check_literals.py counts the two grandfathered literals `5 5` as read twice and the baseline line is deleted."""
import sys, pathlib, shutil
root = pathlib.Path(sys.argv[1]); here = pathlib.Path(__file__).parent
import re
def _chunks(t):
    return re.split(r"(?m)^(?=## `)", t)
def _put(page, heading):
    src = _chunks((here / page).read_text()); dst_t = (root / page).read_text(); dst = _chunks(dst_t)
    tag = "## `" + heading + "`"
    i = [k for k, c in enumerate(dst) if c.startswith(tag)]; j = [k for k, c in enumerate(src) if c.startswith(tag)]
    assert len(i) == 1 and len(j) == 1
    dst[i[0]] = src[j[0]]; (root / page).write_text("".join(dst))
with open(root / "scripts/trust/literal_readings.txt", "a") as f:
    f.write("Checked.Cosmography.CCS.lookback_fifth_order Checked.Trust.SecondReading.gelfandSixthTurn\n")
p = root / "scripts/trust/literal_baseline.txt"
lines = p.read_text().splitlines(keepends=True)
keep = [l for l in lines if not l.startswith("Checked.Cosmography.CCS.lookback_fifth_order |")]
assert len(keep) == len(lines) - 1
p.write_text("".join(keep))
with open(root / "LEDGER.md", "a") as f:
    f.write("- 2026-11-25, run 2026-11-25T0828Z — **Reading registered:** `lookback_fifth_order` now lists the blind reader's `gelfandSixthTurn` in `scripts/trust/literal_readings.txt`; its line of `literal_baseline.txt` is removed (no uncovered literal is left).\n")
for n in ("CLAIMS.md", "CLAIMS_READER.md"):
    _put(n, "lookback_fifth_order")
