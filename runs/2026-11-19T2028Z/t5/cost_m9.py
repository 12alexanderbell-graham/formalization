"""Cost of rule M9 (run 2026-11-19T2028Z): M6 findings on every record line about a listed headline with and without
M9 (base: empty files, so every line is read). Run from scripts/trust: python3 ../../runs/2026-11-19T2028Z/t5/cost_m9.py"""
import sys, re
sys.path.insert(0, '.')
import check_headline_mentions as c
hf = c.files_at(None)
def m6set():
    errs = c.run({k: "" for k in hf}, hf)
    return {e for e in errs if ": M6 " in e}
with_m9 = m6set()
c.M9_REF_RE = re.compile(r"(?!x)x")
without = m6set()
new = sorted(with_m9 - without)
print(len(with_m9), len(without), "M9-only:", len(new))
for e in new[:40]: print(e[:230])
