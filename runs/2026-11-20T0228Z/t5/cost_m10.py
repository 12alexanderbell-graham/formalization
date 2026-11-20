"""Cost of rule M10 (run 2026-11-20T0228Z): M6 findings on every record line about a listed headline with and without
M10 (base: empty files, so every line is read), and on the lines written since M9's commit 4a0ba78 (lines absent from
4a0ba78^). Run from scripts/trust: python3 ../../runs/2026-11-20T0228Z/t5/cost_m10.py"""
import sys
sys.path.insert(0, '.')
import check_headline_mentions as c
hf = c.files_at(None)
old = {c.ident(l) for t in c.files_at("4a0ba78^").values() for l in t.splitlines()}
def m6set():
    errs = c.run({k: "" for k in hf}, hf)
    return {e for e in errs if ": M6 " in e}
with_m10 = m6set()
c.m10_eponym_ref = lambda k: False
without = m6set()
new = sorted(with_m10 - without)
print("all record lines: M6 findings with M10", len(with_m10), "without", len(without), "M10-only:", len(new))
recent = []
for e in new:
    path, n = e.split(":")[0], int(e.split(":")[1])
    line = hf[path].splitlines()[n - 1]
    if c.ident(line) not in old:
        recent.append(e)
print("M10-only findings on lines written since 4a0ba78:", len(recent))
for e in recent[:40]: print(e[:230])
for e in new[:25]: print("  ", e[:200])
