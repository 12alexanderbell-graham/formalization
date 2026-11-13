import Mathlib

/-!
# Falkner–Skan reversed-flow row β = −0.01 of Ganapol 2010 Table 7: wall-shear window of the second branch (FROZEN, run 2026-11-13T0628Z; statements unchanged, proofs added)

Parts 2/5. The statement `fs_neg1988_reversed` of `Work/FalknerSkan/Neg1988Rev.lean` (blind-restated and closed in
run 2026-11-11T1228Z) with β and the window replaced (ten decimals), as in `Work/FalknerSkan/ReversedRows.lean`,
emitted by `runs/2026-11-13T0628Z/scripts/make_row1.py` (copy of this run's `make_row2.py`; proof route: the stack with the shear clamp at 4, `Checked/FSRevW/`) from `runs/2026-11-12T2228Z/scripts/rows_rev.json` (float
shooting `runs/2026-11-12T1828Z/scripts/shoot_rev.py`: q(0) ≈ -0.04232092604).
Do not change the statements; prove them.
-/

namespace Work.FalknerSkan.ReversedRowOne

open Set Filter Topology

/-- Falkner–Skan with β = −1/100: there is a solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0
on [0, ∞) with f(0) = 0, p(0) = 0, p → 1, −1 ≤ p ≤ 1 on [0, ∞) and, for every M, eventually
M (1 − p) ≤ q, whose wall value satisfies -0.0423209261 < q(0) < -0.0423209260 (reversed flow at the wall). -/
theorem fs_rev_one_exists :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1 / 100) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧
      -0.0423209261 < q 0 ∧ q 0 < -0.0423209260 := sorry

end Work.FalknerSkan.ReversedRowOne
