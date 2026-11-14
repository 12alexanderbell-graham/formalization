import sys, os
root = sys.argv[1]
os.chdir(root)
sys.path.insert(0, os.path.join(root, "scripts/trust"))
import check_findings as CF
p = "FINDINGS.md"
t = open(p, encoding="utf-8").read()
# F8 certifies only three sizes (no printed value). A record header line in its notes (accepted: it is indented) makes the
# generated heading, Printed line and Correct line of F8 present the Falkner-Skan separation record F12_separation:
# a printed value "read blind" with a reader's source description, and a Correct clause, in a finding about sizes.
anchor = "  - *(author)* **Errata / prior art:**"
k = t.index("### F8 ")
i = t.index(anchor, k)
t = t[:i] + "  - `Checked.Records.F12_separation`, as Lean states it:\n" + t[i:]
cb = CF.claims_blocks(open("CLAIMS.md", encoding="utf-8").read())
norec = CF.load_baseline(CF.NORECORD)
phr = CF.load_phrases()
body = CF.sections_full(t)["F8"]
lines = body.split("\n")
assert CF.PRINTED_GEN.match(lines[1]) and CF.CORRECT_GEN.match(lines[2])
new = [CF.generated_heading("F8", body, cb, norec), CF.generated_printed("F8", body, cb), CF.generated_correct("F8", body, cb, phr)]
t = t.replace("\n".join(lines[:3]), "\n".join(new))
open(p, "w", encoding="utf-8").write(t)
l = open("LEDGER.md", encoding="utf-8").read()
l += "- 2026-11-14, run 2026-11-14T0028Z - `FINDINGS.md` `F8`: notes reordered, layout regenerated.\n"
open("LEDGER.md", "w", encoding="utf-8").write(l)
