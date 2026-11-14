#!/usr/bin/env python3
"""d06: parser differential. The generators (record_items) read FINDINGS.md with str.splitlines(), which also splits at U+2028,
while FB10/FB14/check_numbers read it with split("\\n") and `^...$` regexes. One indented note line of F14 therefore carries
a block opener, a record header and a quantifier line of a record that no checker sees (they are 'one author note'), and the
generators read them as a second block: the generated heading, Printed and Correct lines of F14 are recomputed from that text
(as the author's own generator run would), so FB10/FB13/FB9 compare them with themselves."""
import importlib, os, re, subprocess, sys
root = os.path.abspath(sys.argv[1])
os.chdir(root)
def run(*a):
    r = subprocess.run(a, cwd=root, capture_output=True, text=True)
    assert r.returncode == 0, (a, r.stdout[-2000:], r.stderr[-2000:])
LS = " "
p = root + "/FINDINGS.md"
s = open(p, encoding="utf-8").read()
anchor = "  - *(author)* **Fidelity audit:** blind restatement closed in `Work/FalknerSkan/Neg1988RevBlindClosed.lean` (run 2026-11-11T1228Z)."
assert s.count(anchor) == 1
# the two stray backticks keep the Lean citation rule of StatementDeps.lean (which splits the file at backticks and reads
# the odd tokens without spaces as names) off the planted record name; the planted text between them holds an even number
REC = "F14_reversed_wall_shear_unique"
planted = (anchor + " `" + LS + "<!-- certified: " + REC + " -->" + LS
           + "  - `Checked.Records." + REC + "`, as Lean states it:" + LS
           + "    > **For every** `f : ℝ → ℝ`, `p : ℝ → ℝ`, `q : ℝ → ℝ`:" + LS + "<!-- /certified -->" + LS + "`")
s = s.replace(anchor, planted)
open(p, "w", encoding="utf-8").write(s)
sys.path.insert(0, root + "/scripts/trust")
cf = importlib.import_module("check_findings")
text = open(p, encoding="utf-8").read()
cb = cf.claims_blocks(open(root + "/CLAIMS.md", encoding="utf-8").read())
ph = cf.load_phrases()
norec = cf.load_baseline(cf.NORECORD)
body = cf.sections_full(text)["F14"]
lines = body.split("\n")
new = list(lines)
new[0] = cf.generated_heading("F14", body, cb, norec)
for i, l in enumerate(lines):
    if cf.PRINTED_GEN.match(l):
        new[i] = cf.generated_printed("F14", body, cb)
    elif cf.CORRECT_GEN.match(l):
        new[i] = cf.generated_correct("F14", body, cb, ph)
nb = "\n".join(new)
assert text.count(body) == 1
open(p, "w", encoding="utf-8").write(text.replace(body, nb))
run("python3", "scripts/trust/check_numbers.py", "--write")
run("python3", "validation/make_packet.py")
led = root + "/LEDGER.md"
t = open(led, encoding="utf-8").read()
if not t.endswith("\n"):
    t += "\n"
t += ("- 2026-11-14, run 2026-11-14T1428Z — `FINDINGS.md`: finding `F14` notes extended and its generated heading, Printed "
      "and Correct lines regenerated.\n")
open(led, "w", encoding="utf-8").write(t)
