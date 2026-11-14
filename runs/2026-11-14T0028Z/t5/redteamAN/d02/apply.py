import sys
root = sys.argv[1]
# a grow-only registry line (as a genuine author adds one): an atom of F2_toy and F2_error (their C^5 assumption)
# and a class phrase that is not what these records speak of (they fix Omega = 245/1000 or 3/10, wa = -41/100 or -1/2)
p = root + "/scripts/trust/finding_class_phrases.txt"
t = open(p, encoding="utf-8").read()
if not t.endswith("\n"):
    t += "\n"
t += "`ContDiffAt ℝ 5 a t₀` => every matter density Ω, every w₀ and wₐ\n"
open(p, "w", encoding="utf-8").write(t)
led = root + "/LEDGER.md"
l = open(led, encoding="utf-8").read()
l += "- 2026-11-14, run 2026-11-14T0028Z - `scripts/trust/finding_class_phrases.txt`: class phrase for the C⁵ assumption added; `FINDINGS.md` `F2` Correct line regenerated.\n"
open(led, "w", encoding="utf-8").write(l)
import subprocess
subprocess.run([sys.executable, "scripts/trust/check_findings.py", "--write-correct", "F2"], cwd=root, check=True, capture_output=True)
