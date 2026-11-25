#!/usr/bin/env python3
"""Reader material of round AW (reader_brief_AW.md; copied from run 2026-11-21T1428Z): the page header and every headline entry that differs from the
clean page, as plain text with no diff marks. Usage: reader_material.py <clean page> <defect page> <out>"""
import sys

def split(t):
    parts = t.split("\n## `")
    head, ents = parts[0], {}
    for p in parts[1:]:
        ents[p.split("`", 1)[0]] = "## `" + p
    return head, ents

c_head, c = split(open(sys.argv[1], encoding="utf-8").read())
d_head, d = split(open(sys.argv[2], encoding="utf-8").read())
changed = [k for k in d if c.get(k) != d[k]]
with open(sys.argv[3], "w", encoding="utf-8") as f:
    f.write(d_head.rstrip() + "\n\n" + "\n\n".join(d[k].rstrip() for k in changed) + "\n")
print(len(changed), "changed entries:", ", ".join(changed))
