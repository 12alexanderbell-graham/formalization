import sys, os
root = sys.argv[1]
def sub(path, old, new):
    p = os.path.join(root, path)
    s = open(p, encoding="utf-8").read()
    assert s.count(old) == 1, (path, old, s.count(old))
    open(p, "w", encoding="utf-8").write(s.replace(old, new))
R = "scripts/trust/phrase_roles.txt"
B = "scripts/trust/phrase_clause_baseline.txt"
line = "CLAUSE | Checked.Chemistry.Coexistence.IsMaxwellCoexistence | equivalent to equal chemical potential in both phases"
# 1. shrink the exclusion baseline (allowed: shrink-only)
sub(B, line + "\n", "")
# 2. show the reader line (P9: every non-excluded reader line of a cited source is in the registry)
anchor = "CLAUSE | Checked.Chemistry.Coexistence.IsMaxwellCoexistence | pressure is a function of molar volume at fixed temperature\n"
sub(R, anchor, anchor + line + "\n")
# 3. the phrase as the generator prints it (clause order = registry order)
sub("scripts/trust/phrases.txt",
    "pressure is a function of molar volume at fixed temperature)",
    "pressure is a function of molar volume at fixed temperature; equivalent to equal chemical potential in both phases)")
with open(os.path.join(root, "LEDGER.md"), "a", encoding="utf-8") as f:
    f.write("\n- 2026-11-09, run 2026-11-09T1428Z: phrase of `IsMaxwellCoexistence` regenerated from the blind registry after the reader line `equivalent to equal chemical potential in both phases` left the shrink-only exclusion baseline `phrase_clause_baseline.txt` (reason (5) no longer applies: the pin theorem has a proof from the equal-chemical-potential law).\n")
