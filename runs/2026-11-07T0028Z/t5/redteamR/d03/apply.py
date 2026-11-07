#!/usr/bin/env python3
"""d03: new COMPOSITE definition IsDecelerating a t := decel a t < 0 (the sign is the wrong way round for the name:
decel < 0 means ACCELERATING expansion) and headline exp_scale_factor_decelerating (de Sitter, a = exp).
usage: apply.py <repo_root>"""
import sys
from pathlib import Path

root = Path(sys.argv[1])


def append(rel, text):
    p = root / rel
    old = p.read_text(encoding="utf-8")
    if not old.endswith("\n"):
        old += "\n"
    p.write_text(old + text, encoding="utf-8")


LEAN = '''import Checked.Cosmography.Lookback
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

/-! The exponential scale factor and the sign of its deceleration parameter. -/

namespace Checked.Cosmography.DeSitter

/-- The expansion of the scale factor `a` is decelerating at time `t`. -/
def IsDecelerating (a : ℝ → ℝ) (t : ℝ) : Prop := decel a t < 0

/-- The deceleration parameter of the exponential scale factor is -1 at every time. -/
theorem exp_decel (t : ℝ) : decel Real.exp t = -1 := by
  have h2 : Real.exp t ^ 2 ≠ 0 := pow_ne_zero 2 (Real.exp_pos t).ne'
  first
    | (simp only [decel, Real.deriv_exp]; rw [div_eq_iff h2]; ring; done)
    | (simp [decel, Real.deriv_exp]; field_simp; done)

/-- The scale factor `Real.exp` is decelerating at every time `t`. -/
theorem exp_scale_factor_decelerating (t : ℝ) : IsDecelerating Real.exp t := by
  unfold IsDecelerating
  rw [exp_decel]
  norm_num

end Checked.Cosmography.DeSitter
'''

new = root / "Checked/Cosmography/DeSitterDeceleration.lean"
assert not new.exists()
new.write_text(LEAN, encoding="utf-8")
append("Checked.lean", "import Checked.Cosmography.DeSitterDeceleration\n")
append("scripts/trust/headlines.txt",
       "# Exponential scale factor (run 2026-11-07T0228Z)\nChecked.Cosmography.DeSitter.exp_scale_factor_decelerating\n")
append("scripts/trust/def_kinds.txt", "Checked.Cosmography.DeSitter.IsDecelerating COMPOSITE\n")
append("LEDGER.md",
       "\n## Run 2026-11-07T0228Z (author, part 5)\n"
       "- New headline `exp_scale_factor_decelerating` (module `Checked.Cosmography.DeSitter`, headlines.txt) with its predicate `IsDecelerating` "
       "(def_kinds.txt, COMPOSITE: one pinned definition compared with 0, no numeral other than 0). UNCONDITIONAL (one real binder). "
       "No frozen constant, pin, phrase or registry line changed.\n")
print("d03 applied")
