import Checked.Trust.NonVacuity
import Checked.FalknerSkan.Limit
/-! Necessity of the third-order system's first equation (f has derivative p) in `Checked.FalknerSkan.Limit.fs_monotone_of_limit`. Without it f is any function with f(0) = 0, and the third equation only asks that the derivative of q equal −f q − β(1 − p²): wherever q is not zero, f can be solved for. The witness takes β = 1 and a velocity profile p that is a polynomial of degree six in one minus the reciprocal of one plus the height: zero at the wall with zero shear there and second derivative minus one, dipping to minus two at height one (shear zero there again, second derivative three = β(p² − 1)), and tending to one. Its shear vanishes only at those two heights, where the third equation holds whatever f is; at every other height f is read off the equation. The wall shear is zero, so the conclusion fails at the wall. Module `NecessityBC`. -/

namespace Checked.Trust.NCBC
open Set Filter Topology

/-- The profile polynomial ncbcPhi (ncbcPhi(0) = 0, ncbcPhi(1/2) = −2, ncbcPhi(1) = 1). -/
noncomputable def ncbcPhi (x : ℝ) : ℝ := 132 * x ^ 6 - 386 * x ^ 5 + 381 * x ^ 4 - 251 / 2 * x ^ 3 - 1 / 2 * x ^ 2
/-- Its derivative: x times (x minus one half) times the positive cubic of `ncbcL_pos`. -/
noncomputable def ncbcPhi1 (x : ℝ) : ℝ := 792 * x ^ 5 - 1930 * x ^ 4 + 1524 * x ^ 3 - 753 / 2 * x ^ 2 - x
/-- Its second derivative. -/
noncomputable def ncbcPhi2 (x : ℝ) : ℝ := 3960 * x ^ 4 - 7720 * x ^ 3 + 4572 * x ^ 2 - 753 * x - 1

lemma ncbcPhi_deriv (x : ℝ) : HasDerivAt ncbcPhi (ncbcPhi1 x) x := by
  have h := ((((hasDerivAt_pow 6 x).const_mul 132).sub ((hasDerivAt_pow 5 x).const_mul 386)).add
    ((hasDerivAt_pow 4 x).const_mul 381)).sub (((hasDerivAt_pow 3 x).const_mul (251 / 2)).add
    ((hasDerivAt_pow 2 x).const_mul (1 / 2)))
  convert h using 1
  · funext y; simp only [ncbcPhi, Pi.add_apply, Pi.sub_apply]; ring
  · simp only [ncbcPhi1]; push_cast; ring

lemma ncbcPhi1_deriv (x : ℝ) : HasDerivAt ncbcPhi1 (ncbcPhi2 x) x := by
  have h := ((((hasDerivAt_pow 5 x).const_mul 792).sub ((hasDerivAt_pow 4 x).const_mul 1930)).add
    ((hasDerivAt_pow 3 x).const_mul 1524)).sub (((hasDerivAt_pow 2 x).const_mul (753 / 2)).add
    (hasDerivAt_id x))
  convert h using 1
  · funext y; simp only [ncbcPhi1, Pi.add_apply, Pi.sub_apply, id]; ring
  · simp only [ncbcPhi2]; push_cast; ring

/-- The cubic factor of the derivative is positive for every nonnegative argument. -/
lemma ncbcL_pos (x : ℝ) (hx : 0 ≤ x) : 0 < 792 * x ^ 3 - 1534 * x ^ 2 + 757 * x + 2 := by
  nlinarith [sq_nonneg (x - 24 / 25), sq_nonneg (x - 1 / 3), mul_nonneg hx (sq_nonneg (x - 24 / 25)),
    mul_nonneg hx (sq_nonneg (x - 1 / 3))]

lemma ncbcPhi1_eq (x : ℝ) : ncbcPhi1 x = x * (x - 1 / 2) * (792 * x ^ 3 - 1534 * x ^ 2 + 757 * x + 2) := by
  simp only [ncbcPhi1]; ring

/-- The reciprocal of one plus the height; the profile is read at one minus it. -/
noncomputable def ncbcW (η : ℝ) : ℝ := (1 + η)⁻¹

noncomputable def ncbcP (η : ℝ) : ℝ := ncbcPhi (1 - ncbcW η)
noncomputable def ncbcQ (η : ℝ) : ℝ := ncbcPhi1 (1 - ncbcW η) * ncbcW η ^ 2
noncomputable def ncbcR (η : ℝ) : ℝ := ncbcPhi2 (1 - ncbcW η) * ncbcW η ^ 4 - 2 * ncbcPhi1 (1 - ncbcW η) * ncbcW η ^ 3
/-- The free function: whatever makes the third equation hold where the shear is not zero. -/
noncomputable def ncbcF (η : ℝ) : ℝ := -(ncbcR η + 1 * (1 - ncbcP η ^ 2)) / ncbcQ η

lemma ncbcW_deriv (η : ℝ) (hη : 0 ≤ η) : HasDerivAt ncbcW (-(ncbcW η ^ 2)) η := by
  have h1 : (1 + η) ≠ 0 := by linarith
  have h := (hasDerivAt_inv h1).comp η ((hasDerivAt_id η).const_add 1)
  have e : (fun y : ℝ => y⁻¹) ∘ HAdd.hAdd 1 = ncbcW := by funext x; simp [ncbcW]
  rw [e] at h
  convert h using 1
  simp [ncbcW, inv_pow]

lemma ncbcW_pos (η : ℝ) (hη : 0 ≤ η) : 0 < ncbcW η := inv_pos.2 (by linarith)
lemma ncbcW_le (η : ℝ) (hη : 0 ≤ η) : ncbcW η ≤ 1 := inv_le_one_of_one_le₀ (by linarith)

lemma ncbcP_deriv (η : ℝ) (hη : 0 ≤ η) : HasDerivAt ncbcP (ncbcQ η) η := by
  have h := (ncbcPhi_deriv (1 - ncbcW η)).comp η ((ncbcW_deriv η hη).const_sub 1)
  have e : ncbcPhi ∘ (fun x => 1 - ncbcW x) = ncbcP := rfl
  rw [e] at h
  convert h using 1
  simp only [ncbcQ]; ring

lemma ncbcQ_deriv (η : ℝ) (hη : 0 ≤ η) : HasDerivAt ncbcQ (ncbcR η) η := by
  have h1 := (ncbcPhi1_deriv (1 - ncbcW η)).comp η ((ncbcW_deriv η hη).const_sub 1)
  have h := h1.mul ((ncbcW_deriv η hη).pow 2)
  have e : (ncbcPhi1 ∘ fun x => 1 - ncbcW x) * ncbcW ^ 2 = ncbcQ := by funext x; simp [ncbcQ]
  rw [e] at h
  convert h using 1
  simp only [ncbcR, Function.comp, Pi.pow_apply]; push_cast; ring

lemma ncbcQ_zero (η : ℝ) (hη : 0 ≤ η) (h : ncbcQ η = 0) : ncbcR η = -(1 * (1 - ncbcP η ^ 2)) := by
  have hw := ncbcW_pos η hη
  have hw1 := ncbcW_le η hη
  have h' : ncbcPhi1 (1 - ncbcW η) = 0 := by
    simp only [ncbcQ] at h
    rcases mul_eq_zero.1 h with h | h
    · exact h
    · exact absurd ((pow_eq_zero_iff two_ne_zero).1 h) hw.ne'
  have hL := ncbcL_pos (1 - ncbcW η) (by linarith)
  rw [ncbcPhi1_eq] at h'
  rcases mul_eq_zero.1 h' with h'' | h''
  · rcases mul_eq_zero.1 h'' with h3 | h3
    · have : ncbcW η = 1 := by linarith
      simp only [ncbcR, ncbcP, ncbcPhi, ncbcPhi1, ncbcPhi2, this]; norm_num
    · have : ncbcW η = 1 / 2 := by linarith
      simp only [ncbcR, ncbcP, ncbcPhi, ncbcPhi1, ncbcPhi2, this]; norm_num
  · exact absurd h'' hL.ne'

lemma ncbcP_lim : Tendsto ncbcP atTop (𝓝 1) := by
  have hw : Tendsto ncbcW atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ 1 tendsto_id)
  have hs : Tendsto (fun η => 1 - ncbcW η) atTop (𝓝 (1 - 0)) := tendsto_const_nhds.sub hw
  have hc : Continuous ncbcPhi := by unfold ncbcPhi; fun_prop
  have := (hc.tendsto (1 - 0)).comp hs
  have e : ncbcPhi (1 - 0) = 1 := by simp only [ncbcPhi]; norm_num
  rw [e] at this
  exact this

/-- The first equation (f has derivative p) is needed in `fs_monotone_of_limit`: with f free, a profile
that dips below minus one before tending to one, with zero shear at the wall, meets every other
hypothesis. -/
theorem fs_monotone_of_limit_h3 : necessity% Checked.FalknerSkan.Limit.fs_monotone_of_limit 3 := by
  have q0 : ncbcQ 0 = 0 := by simp [ncbcQ, ncbcW, ncbcPhi1]
  refine ⟨1, one_pos, le_rfl, ncbcF, ncbcP, ncbcQ, fun η hη => (ncbcP_deriv η hη).hasDerivWithinAt,
    fun η hη => ?_, ?_, by simp [ncbcP, ncbcW, ncbcPhi], ncbcP_lim, 0, mem_Ici.2 le_rfl, by rw [q0]; exact lt_irrefl 0⟩
  · refine (ncbcQ_deriv η hη).hasDerivWithinAt.congr_deriv ?_
    by_cases h : ncbcQ η = 0
    · rw [ncbcQ_zero η hη h, h]; simp [ncbcF, h]
    · simp only [ncbcF]; field_simp; ring
  · simp [ncbcF, q0]

end Checked.Trust.NCBC
