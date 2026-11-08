"""One-off migration (run 2026-11-08T0628Z): write the role Lean gives each certified value into its
FINDINGS.md tag (rule R0 of check_numbers.py). Roles come from .lake/records_numbers.tsv and def_kinds.txt
through check_numbers.role_of; a tag that already names a role is left alone."""
import re, sys
sys.path.insert(0, "scripts/trust")
import check_numbers as c
tsv = sys.argv[1] if len(sys.argv) > 1 else c.TSV
rows = [l.split("\t") for l in open(tsv, encoding="utf-8").read().splitlines() if l.strip()]
k = c.load_kinds()
roles = {}
for r in rows:
    roles.setdefault(r[0], []).append((r[1], c.parse_sel_tsv(r[2]), c.role_of(r[3], k)))
text = open(c.FINDINGS, encoding="utf-8").read()
cut = text.find("\n" + c.GENERATED)
head, tail = (text[:cut], text[cut:]) if cut >= 0 else (text, "")
def fix(m):
    num, name, sel = m.group(1), m.group(2), m.group(3)
    items = [x.strip() for x in sel.split(",")] if sel else []
    if any(x in c.ROLES for x in items):
        return m.group(0)
    seltup = c.parse_sel_tag(", ".join(items)) if items else ("", frozenset())
    cand = [r for v, s_, r in roles.get(name, []) if c.value(v) == c.value(num) and (not items or s_ == seltup)]
    if not cand:
        cand = [r for v, s_, r in roles.get(name, []) if c.value(v) == c.value(num)]
    if len(set(cand)) != 1 or cand[0] == "free":
        return m.group(0)
    rr = "difference" if cand[0].startswith("difference(") else cand[0]
    return f"{num}[✓{name}({', '.join(items + [rr])})]"
new = re.sub(r"(" + c.NUM + r")\[✓([A-Za-z0-9_]+)(?:\(([^()\[\]]*)\))?\]", fix, head)
open(c.FINDINGS, "w", encoding="utf-8").write(new + tail)
print("changed tags:", sum(1 for a, b in zip(re.findall(r"\[✓[^\]]*\]", head), re.findall(r"\[✓[^\]]*\]", new)) if a != b))
