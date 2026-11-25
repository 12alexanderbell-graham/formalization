#!/usr/bin/env python3
"""d02: register the blind reader constant b1a3Modulus (5 * Real.logb 10 x, binder x) for l19_sq_central; its wildcard x
swallows the fit coefficients 3.075 4.466 3.716, which check_literals.py then counts as covered; the baseline line shrinks."""
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
def sub(path, old, new):
    p = root / path; t = p.read_text(); assert t.count(old) == 1, (path, old[:40]); p.write_text(t.replace(old, new))
with open(root / "scripts/trust/literal_readings.txt", "a") as f:
    f.write("Checked.Cosmography.B1L19.l19_sq_central Checked.Trust.SecondReading.b1a3Modulus\n")
sub("scripts/trust/literal_baseline.txt",
    "Checked.Cosmography.B1L19.l19_sq_central | 1 3 1 2 2 1 4 2 1 5 10 3.075 4.466 3.716 5 10 3.075 4.466 3.716 |",
    "Checked.Cosmography.B1L19.l19_sq_central | 1 3 1 2 2 1 4 2 1 |")
with open(root / "LEDGER.md", "a") as f:
    f.write("- 2026-11-25, run 2026-11-25T0828Z — **Reading registered:** `l19_sq_central` now lists the blind reader's `b1a3Modulus` in `scripts/trust/literal_readings.txt`; its grandfathered literal list in `literal_baseline.txt` shrinks accordingly.\n")
for n in ("CLAIMS.md", "CLAIMS_READER.md"):
    _put(n, "l19_sq_central")
