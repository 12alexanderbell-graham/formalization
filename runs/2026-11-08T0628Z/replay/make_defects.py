"""Replay of the open role defects of the adversary of run 2026-11-08T0028Z (d1, d2, d5, d6; their diffs
were written against FINDINGS.md at 2b219cb) on the current FINDINGS.md, plus variants that avoid the
role words. Writes defects/<id>/FINDINGS.md; judge with check_numbers.py (after StatementDeps)."""
import os, sys
src = open("FINDINGS.md", encoding="utf-8").read()
D = {
 "d1": ("the printed l₀ is 0.685[✓F1_printedL0(printed)] instead of 3.115[✓F1_l0(derived)]",
        "the printed l₀ is 3.115[✓F1_l0(derived)] instead of 0.685[✓F1_printedL0(printed)]"),
 "d1b": ("the printed l₀ is 0.685[✓F1_printedL0(printed)] instead of 3.115[✓F1_l0(derived)]",
         "the formula's l₀ is 3.115[✓F1_l0(derived)] instead of 0.685[✓F1_printedL0(printed)]"),
 "d1c": ("the printed l₀ is 0.685[✓F1_printedL0(printed)] instead of 3.115[✓F1_l0(derived)]",
         "the printed l₀ is 3.115[✓F1_l0] instead of 0.685[✓F1_printedL0]"),
 "d2": ("true 0.809[✓F2_toy(cosmoCoeff, derived)], printed −0.906[✓F2_toy(printed)]",
        "true −0.906[✓F2_toy(printed)], printed 0.809[✓F2_toy(cosmoCoeff, derived)]"),
 "d5": ("the printed F(R₀)/(6H₀²) is 0.0462[✓F9_values(printed)] instead of −0.875[✓F9_values(derived)]",
        "the printed F(R₀)/(6H₀²) is −0.875[✓F9_values(derived)] instead of 0.0462[✓F9_values(printed)]"),
 "d5b": ("the printed F(R₀)/(6H₀²) is 0.0462[✓F9_values(printed)] instead of −0.875[✓F9_values(derived)]",
         "F(R₀)/(6H₀²) from it is −0.875[✓F9_values(derived)] instead of 0.0462[✓F9_values(printed)]"),
 "d6": ("(≈ +0.24[✓F3_D4_LCDM(difference)] at q₀ = −0.55[✓F3_D4_LCDM(decel, derived)]",
        "(≈ −0.55[✓F3_D4_LCDM(decel, derived)] at q₀ = +0.24[✓F3_D4_LCDM(difference)]"),
 "d7x": ("true 0.2153[✓F3_D4_LCDM(correctD4, derived)] vs printed 0.4555[✓F3_D4_LCDM(printedD4, printed)]",
         "true 0.4555[✓F3_D4_LCDM(printedD4, printed)] vs printed 0.2153[✓F3_D4_LCDM(correctD4, derived)]"),
 "d8x": ("any w₀: true − printed =", "any w₀: printed − true ="),
}
out = sys.argv[1]
for k, (a, b) in D.items():
    assert src.count(a) == 1, (k, a)
    os.makedirs(f"{out}/{k}", exist_ok=True)
    open(f"{out}/{k}/FINDINGS.md", "w", encoding="utf-8").write(src.replace(a, b))
print("wrote", len(D))
