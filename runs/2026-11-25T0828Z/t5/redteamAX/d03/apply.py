#!/usr/bin/env python3
"""d03: `source=Taylor` on a Lane-Emden headline: the word occurs in the reader's sources clause ("Taylor ODE integration")."""
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
    f.write("Checked.Math.LaneEmden32.laneEmden32_constants source=Taylor Checked.Trust.SecondReading.le32Rhs\n")
with open(root / "LEDGER.md", "a") as f:
    f.write("- 2026-11-25, run 2026-11-25T0828Z — **Source name registered:** `laneEmden32_constants` lists the source name Taylor for the blind reader's `le32Rhs` in `scripts/trust/literal_readings.txt`.\n")
for n in ("CLAIMS.md", "CLAIMS_READER.md"):
    _put(n, "laneEmden32_constants")
