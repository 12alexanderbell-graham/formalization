#!/usr/bin/env python3
"""Run 2026-11-09T1628Z: after promote_fsneg_tenth.py, rewrite the four headline docstrings in Checked in the generated
claim's words (pattern runs/2026-11-09T1028Z/scripts/fix_docs.py: `∀ᶠ` conditions as the claim's own code, no
'eventually', 'two', 'reversed', 'window'). Statements unchanged."""
import re, pathlib
ROOT = pathlib.Path(__file__).resolve().parents[3]
DEC = "for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`"
DEC2 = "for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p₂ η) ≤ q₂ η`"
EQ = "f''' + f f'' + β(1 − f'²) = 0 on [0, ∞)"
DOCS = {
 ("Checked/FalknerSkan/NegWindow.lean", "fs_neg_tenth_window"):
  "Falkner–Skan with β = −1/10: if (f, p, q) is a solution of " + EQ + " with\nf(0) = 0, p(0) = 0, p → 1, q > 0 on [0, ∞) and, " + DEC + ", then\n0.3192697598 < q(0) < 0.3192697599.",
 ("Checked/FalknerSkan/NegWindow.lean", "fs_neg_tenth_monotone_lt"):
  "Falkner–Skan with β = −1/10: if (f, p, q) is a solution of " + EQ + " with\nf(0) = 0, p(0) = 0, p → 1 and q > 0 on [0, ∞), then q(0) < 0.3192697599.",
 ("Checked/FalknerSkan/NegReversed.lean", "fs_neg_tenth_reversed"):
  "Falkner–Skan with β = −1/10: there is a solution (f, p, q) of " + EQ + " with\nf(0) = 0, p(0) = 0, p → 1, −1 ≤ p ≤ 1 on [0, ∞) and, " + DEC + ", with\n−0.1405462131 < q(0) < −0.1405462129.",
 ("Checked/FalknerSkan/NegReversed.lean", "fs_neg_tenth_two_decay"):
  "Falkner–Skan with β = −1/10: there are solutions (f, p, q) and (f₂, p₂, q₂) of\n" + EQ + ", both with f(0) = 0, p(0) = 0, p → 1 and −1 ≤ p ≤ 1 on [0, ∞), with\nq(0) ≠ q₂(0), such that, " + DEC + ", and,\n" + DEC2 + ".",
}
for (f, thm), doc in DOCS.items():
    p = ROOT / f; s = p.read_text(encoding="utf-8")
    s, k = re.subn(r"/--(?:(?!-/).)*?-/\s*\ntheorem " + thm + r"\b", lambda m: f"/-- {doc} -/\ntheorem {thm}", s, count=1, flags=re.S)
    assert k == 1, (f, thm); p.write_text(s, encoding="utf-8")
print("ok")
