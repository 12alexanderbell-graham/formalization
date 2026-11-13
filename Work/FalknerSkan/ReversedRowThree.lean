import Mathlib
import Checked.FSRev.RAssemble
import Checked.FSRev.RAssembleA
import Checked.FSRev.RThreeOver
import Checked.FSRev.RThreeSlow
import Checked.FSRev.RThreeTube

/-!
# Falkner–Skan reversed-flow row β = −0.03 of Ganapol 2010 Table 7: wall-shear window of the second branch (FROZEN, run 2026-11-13T0228Z; statements unchanged, proofs added)

Parts 2/5. The statement `fs_neg1988_reversed` of `Work/FalknerSkan/Neg1988Rev.lean` (blind-restated and closed in
run 2026-11-11T1228Z) with β and the window replaced (ten decimals), as in `Work/FalknerSkan/ReversedRows.lean`,
emitted by `runs/2026-11-13T0228Z/scripts/make_row3.py` (copy of run 2228Z's `make_table.py`) from `runs/2026-11-12T2228Z/scripts/rows_rev.json` (float
shooting `runs/2026-11-12T1828Z/scripts/shoot_rev.py`: q(0) ≈ -0.08256296512).
Do not change the statements; prove them.
-/

namespace Work.FalknerSkan.ReversedRowThree

open Set Filter Topology

theorem three_sqrtK_pos : 0 < Real.sqrt (100 / 3 : ℝ) := Real.sqrt_pos.2 (by norm_num)

theorem three_hK : (-1 / (100 / 3 : ℝ)) = -3 / 100 := by norm_num

theorem three_lo_bound : (-0.0825629652 : ℝ) < -(476677501479557 / 1000000000000000) / Real.sqrt (100 / 3) := by
  have hs := three_sqrtK_pos
  have h : (476677501479557 / 1000000000000000) / (0.0825629652 : ℝ) < Real.sqrt (100 / 3 : ℝ) := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  rw [neg_div, neg_lt_neg_iff, div_lt_iff₀ hs]
  rw [div_lt_iff₀ (by norm_num)] at h; linarith

theorem three_hi_bound : -(476677501309937 / 1000000000000000) / Real.sqrt (100 / 3) < (-0.0825629651 : ℝ) := by
  have hs := three_sqrtK_pos
  have h : Real.sqrt (100 / 3 : ℝ) < (476677501309937 / 1000000000000000) / (0.0825629651 : ℝ) := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  rw [neg_div, neg_lt_neg_iff, lt_div_iff₀ hs]
  rw [lt_div_iff₀ (by norm_num)] at h; linarith

/-- Falkner–Skan with β = −3/100: there is a solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0
on [0, ∞) with f(0) = 0, p(0) = 0, p → 1, −1 ≤ p ≤ 1 on [0, ∞) and, for every M, eventually
M (1 − p) ≤ q, whose wall value satisfies -0.0825629652 < q(0) < -0.0825629651 (reversed flow at the wall). -/
theorem fs_rev_three_exists :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-3 / 100) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧
      -0.0825629652 < q 0 ∧ q 0 < -0.0825629651 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, w1, w2⟩ :=
    Checked.FSRev.RAssembleA.core_revA (K := 100 / 3) (by norm_num) (L := 7 / 4) (by norm_num) (by norm_num)
      Checked.FSRev.RThreeOver.chain Checked.FSRev.RThreeSlow.chain Checked.FSRev.RThreeTube.tube
  refine ⟨f, p, q, a1, a2, fun η hη => ?_, a4, a5, a6,
    fun η hη => ⟨by linarith [(a7 η hη).1], (a7 η hη).2.le⟩, a8, ?_, ?_⟩
  · rw [← three_hK]; exact a3 η hη
  · have e : (-476677501479557 / 1000000000000000 : ℝ) / Real.sqrt (100 / 3) = -(476677501479557 / 1000000000000000) / Real.sqrt (100 / 3) := by ring
    linarith [three_lo_bound]
  · have e : (-476677501309937 / 1000000000000000 : ℝ) / Real.sqrt (100 / 3) = -(476677501309937 / 1000000000000000) / Real.sqrt (100 / 3) := by ring
    linarith [three_hi_bound]

end Work.FalknerSkan.ReversedRowThree
