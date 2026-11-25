#!/usr/bin/env python3
"""d01: def_kinds.txt relabels the CLAIM `AvilesL0Claim` as PRINTED (it has a Transcriptions agreement theorem, so the label checks accept it); relock of
frozen.txt / TRUST_MAP.md as the author does (TRUST_RELOCK=1 StatementDeps.lean) is carried as relock.patch; LEDGER line names the definition."""
import sys, pathlib, shutil, subprocess
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
p = root / "scripts/trust/def_kinds.txt"; t = p.read_text()
old = "Checked.Cosmography.Aviles.AvilesL0Claim CLAIM\n"; assert t.count(old) == 1
p.write_text(t.replace(old, "Checked.Cosmography.Aviles.AvilesL0Claim PRINTED\n"))
subprocess.run(["git", "-C", str(root), "apply", str(here / "relock.patch")], check=True)
with open(root / "LEDGER.md", "a") as f:
    f.write("- 2026-11-25, run 2026-11-25T0828Z — **Relock entry:** `AvilesL0Claim` is reclassified from CLAIM to PRINTED in `scripts/trust/def_kinds.txt` (it carries a blind second reading, `Checked.Trust.Transcriptions.agree_AvilesL0Claim`); frozen.txt and TRUST_MAP.md relocked.\n")
tp = root / "scripts/trust/claim_templates.txt"; tt = tp.read_text()
line = "Checked.Cosmography.Aviles.AvilesL0Claim 09a7bd6f045d3177\n"; assert tt.count(line) == 1
tp.write_text(tt.replace(line, ""))
with open(root / "LEDGER.md", "a") as f:
    f.write("- 2026-11-25, run 2026-11-25T0828Z — **Template entry:** the frozen template line of `AvilesL0Claim` is removed from `scripts/trust/claim_templates.txt` (the definition is PRINTED now, so its template is no longer frozen there).\n")
for n in ("CLAIMS.md", "CLAIMS_READER.md"):
    _put(n, "avilesL0Claim_false")
