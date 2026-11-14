import sys, os
root = sys.argv[1]
os.chdir(root)
sys.path.insert(0, os.path.join(root, "scripts/trust"))
import check_findings as CF
p = "FINDINGS.md"
t = open(p, encoding="utf-8").read()
# The generators (heading, Printed, Correct) read the records of a section from EVERY line of the form
# '  - `Checked.Records.X`, as Lean states it:', also one that stands indented in the unchecked notes (the layout
# rule accepts any indented line there). One such note line makes F3's generated heading, Printed line and Correct
# line speak of F2_error, a record of another finding with another printed value and another source.
anchor = "  - *(author)* **Errata:** none found (Crossref, web search; arXiv v1, v2 only)."
assert t.count(anchor) == 1
t = t.replace(anchor, "  - `Checked.Records.F2_error`, as Lean states it:\n" + anchor)
cb = CF.claims_blocks(open("CLAIMS.md", encoding="utf-8").read())
norec = CF.load_baseline(CF.NORECORD)
phr = CF.load_phrases()
body = CF.sections_full(t)["F3"]
lines = body.split("\n")
assert lines[0].startswith("### F3") and CF.PRINTED_GEN.match(lines[1]) and CF.CORRECT_GEN.match(lines[2])
new = [CF.generated_heading("F3", body, cb, norec), CF.generated_printed("F3", body, cb), CF.generated_correct("F3", body, cb, phr)]
t = t.replace("\n".join(lines[:3]), "\n".join(new))
open(p, "w", encoding="utf-8").write(t)
led = "LEDGER.md"
l = open(led, encoding="utf-8").read()
l += "- 2026-11-14, run 2026-11-14T0028Z - `FINDINGS.md` `F3`: notes reordered, layout regenerated.\n"
open(led, "w", encoding="utf-8").write(l)
