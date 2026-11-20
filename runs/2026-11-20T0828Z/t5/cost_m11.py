"""Cost of rule M11 (run 2026-11-20T0828Z): M6 findings on every record line about a listed headline with and without
M11 (base: empty files, so every line is read), and on the lines written since M10's commit (lines absent from the
parent of the commit that introduced M10_EPONYMS). Run from scripts/trust: python3 ../../runs/2026-11-20T0828Z/t5/cost_m11.py"""
import sys
sys.path.insert(0, '.')
import check_headline_mentions as c
hf = c.files_at(None)
intro = c.git("log", "--format=%H", "-S", "M10_EPONYMS = frozenset(", "--", "scripts/trust/check_headline_mentions.py").split()[-1]
old = {c.ident(l) for t in c.files_at(intro + "^").values() for l in t.splitlines()}
def m6set():
    errs = c.run({k: "" for k in hf}, hf)
    return {e for e in errs if ": M6 " in e}
with_m11 = m6set()
c.m11_ref = lambda k: False
without = m6set()
new = sorted(with_m11 - without)
print("M10 commit", intro[:8])
print("all record lines: M6 findings with M11", len(with_m11), "without", len(without), "M11-only:", len(new))
recent = []
for e in new:
    path, n = e.split(":")[0], int(e.split(":")[1])
    line = hf[path].splitlines()[n - 1]
    if c.ident(line) not in old:
        recent.append((e, line))
print("M11-only findings on lines written since M10's commit:", len(recent))
for e, line in recent[:40]: print(e[:120], "||", line[:200])
for e in new[:25]: print("  ", e[:200])
