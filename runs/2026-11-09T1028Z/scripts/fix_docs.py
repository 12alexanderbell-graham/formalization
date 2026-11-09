#!/usr/bin/env python3
"""Run 2026-11-09T1028Z: after promote_fsneg.py, rewrite the four headline docstrings in Checked for the claim-vocabulary
rules (check_claim_vocab V1/V14: no words the generated claim lacks) and rename the headline whose Work name says
'not_unique' (V8: a strength word the statement does not contain) in Work and Checked. Statements unchanged."""
import re, pathlib
ROOT = pathlib.Path(__file__).resolve().parents[3]
OLD, NEW = "fs_neg_tenth_not_unique_outside", "fs_neg_tenth_outside_decay"
for f in ["Work/FalknerSkan/NegOutside.lean", "Work/FalknerSkan/NOBlindClosed.lean", "Checked/FalknerSkan/NegOutside.lean",
          "Checked/Trust/Necessity.lean", "scripts/trust/headlines.txt", "scripts/trust/literal_readings.txt"]:
    p = ROOT / f; s = p.read_text(encoding="utf-8"); assert OLD in s or NEW in s, f; p.write_text(s.replace(OLD, NEW), encoding="utf-8")
DEC = "for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`"
DOCS = {
 ("Checked/FalknerSkan/NegDecay.lean", "fs_neg_decay_max_shear"):
  "Falkner–Skan with β < 0: if (f, p, q) is a solution of f''' + f f'' + β(1 − f'²) = 0 on [0, ∞) with\nf(0) = 0, p(0) = 0, p → 1, q > 0 on [0, ∞) and, " + DEC + ", and (f₂, p₂, q₂) is a\nsolution with f₂(0) = 0, p₂(0) = 0, p₂ → 1 and q₂ > 0 on [0, ∞), then q₂(0) ≤ q(0).",
 ("Checked/FalknerSkan/NegDecay.lean", "fs_neg_decay_equal"):
  "Falkner–Skan with β < 0: for every solution (f, p, q) and every solution (f₂, p₂, q₂) of\nf''' + f f'' + β(1 − f'²) = 0 on [0, ∞), both with f(0) = 0, p(0) = 0, p → 1, q > 0 on [0, ∞) and,\n" + DEC + ": f η = f₂ η, p η = p₂ η and q η = q₂ η for every η ≥ 0.",
 ("Checked/FalknerSkan/NegTenth.lean", "fs_neg_tenth_exists_decay"):
  "Falkner–Skan with β = −1/10: there is a solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0 on\n[0, ∞) with f(0) = 0, p(0) = 0, p → 1, q > 0 on [0, ∞) and, " + DEC + ".",
 ("Checked/FalknerSkan/NegOutside.lean", NEW):
  "Falkner–Skan with β = −1/10: there are solutions (f, p, q) and (f₂, p₂, q₂) of\nf''' + f f'' + β(1 − f'²) = 0 on [0, ∞), both with f(0) = 0, p(0) = 0, p → 1, q > 0 and 0 ≤ p ≤ 1 on\n[0, ∞), with q(0) ≠ q₂(0), such that it is not the case that, " + DEC + ", and it is not the case that,\nfor every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p₂ η) ≤ q₂ η`.",
}
for (f, thm), doc in DOCS.items():
    p = ROOT / f; s = p.read_text(encoding="utf-8")
    s, k = re.subn(r"/--(?:(?!-/).)*?-/\s*\ntheorem " + thm + r"\b", lambda m: f"/-- {doc} -/\ntheorem {thm}", s, count=1, flags=re.S)
    assert k == 1, (f, thm); p.write_text(s, encoding="utf-8")
print("ok")
