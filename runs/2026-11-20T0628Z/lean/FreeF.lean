import Mathlib

namespace Scratch.FreeF
open Set Filter Topology

/-- The profile polynomial Φ (Φ(0) = 0, Φ(1/2) = −2, Φ(1) = 1). -/
noncomputable def Φ (x : ℝ) : ℝ := 132 * x ^ 6 - 386 * x ^ 5 + 381 * x ^ 4 - 251 / 2 * x ^ 3 - 1 / 2 * x ^ 2
/-- Its derivative x (x − 1/2) L(x). -/
noncomputable def Φ₁ (x : ℝ) : ℝ := 792 * x ^ 5 - 1930 * x ^ 4 + 1524 * x ^ 3 - 753 / 2 * x ^ 2 - x
/-- Its second derivative. -/
noncomputable def Φ₂ (x : ℝ) : ℝ := 3960 * x ^ 4 - 7720 * x ^ 3 + 4572 * x ^ 2 - 753 * x - 1

lemma Φ_deriv (x : ℝ) : HasDerivAt Φ (Φ₁ x) x := by
  have h := ((((hasDerivAt_pow 6 x).const_mul 132).sub ((hasDerivAt_pow 5 x).const_mul 386)).add
    ((hasDerivAt_pow 4 x).const_mul 381)).sub (((hasDerivAt_pow 3 x).const_mul (251 / 2)).add
    ((hasDerivAt_pow 2 x).const_mul (1 / 2)))
  convert h using 1
  · funext y; simp only [Φ, Pi.add_apply, Pi.sub_apply]; ring
  · simp only [Φ₁]; push_cast; ring

lemma Φ₁_deriv (x : ℝ) : HasDerivAt Φ₁ (Φ₂ x) x := by
  have h := ((((hasDerivAt_pow 5 x).const_mul 792).sub ((hasDerivAt_pow 4 x).const_mul 1930)).add
    ((hasDerivAt_pow 3 x).const_mul 1524)).sub (((hasDerivAt_pow 2 x).const_mul (753 / 2)).add
    (hasDerivAt_id x))
  convert h using 1
  · funext y; simp only [Φ₁, Pi.add_apply, Pi.sub_apply, id]; ring
  · simp only [Φ₂]; push_cast; ring

/-- The cubic factor L(x) = 792x³ − 1534x² + 757x + 2 is positive for x ≥ 0. -/
lemma L_pos (x : ℝ) (hx : 0 ≤ x) : 0 < 792 * x ^ 3 - 1534 * x ^ 2 + 757 * x + 2 := by
  nlinarith [sq_nonneg (x - 24 / 25), sq_nonneg (x - 1 / 3), mul_nonneg hx (sq_nonneg (x - 24 / 25)),
    mul_nonneg hx (sq_nonneg (x - 1 / 3))]

lemma Φ₁_eq (x : ℝ) : Φ₁ x = x * (x - 1 / 2) * (792 * x ^ 3 - 1534 * x ^ 2 + 757 * x + 2) := by
  simp only [Φ₁]; ring

/-- The wall coordinate s = 1 − 1/(1 + η). -/
noncomputable def w (η : ℝ) : ℝ := (1 + η)⁻¹

noncomputable def pW (η : ℝ) : ℝ := Φ (1 - w η)
noncomputable def qW (η : ℝ) : ℝ := Φ₁ (1 - w η) * w η ^ 2
noncomputable def rW (η : ℝ) : ℝ := Φ₂ (1 - w η) * w η ^ 4 - 2 * Φ₁ (1 - w η) * w η ^ 3
/-- The free function: whatever makes the third equation hold where the shear is not zero. -/
noncomputable def fW (η : ℝ) : ℝ := -(rW η + 1 * (1 - pW η ^ 2)) / qW η

lemma w_deriv (η : ℝ) (hη : 0 ≤ η) : HasDerivAt w (-(w η ^ 2)) η := by
  have h1 : (1 + η) ≠ 0 := by linarith
  have h := (hasDerivAt_inv h1).comp η ((hasDerivAt_id η).const_add 1)
  have e : (fun y : ℝ => y⁻¹) ∘ HAdd.hAdd 1 = w := by funext x; simp [w]
  rw [e] at h
  convert h using 1
  simp [w, inv_pow]

lemma w_pos (η : ℝ) (hη : 0 ≤ η) : 0 < w η := inv_pos.2 (by linarith)
lemma w_le (η : ℝ) (hη : 0 ≤ η) : w η ≤ 1 := inv_le_one_of_one_le₀ (by linarith)

lemma pW_deriv (η : ℝ) (hη : 0 ≤ η) : HasDerivAt pW (qW η) η := by
  have h := (Φ_deriv (1 - w η)).comp η ((w_deriv η hη).const_sub 1)
  have e : Φ ∘ (fun x => 1 - w x) = pW := rfl
  rw [e] at h
  convert h using 1
  simp only [qW]; ring

lemma qW_deriv (η : ℝ) (hη : 0 ≤ η) : HasDerivAt qW (rW η) η := by
  have h1 := (Φ₁_deriv (1 - w η)).comp η ((w_deriv η hη).const_sub 1)
  have h := h1.mul ((w_deriv η hη).pow 2)
  have e : (Φ₁ ∘ fun x => 1 - w x) * w ^ 2 = qW := by funext x; simp [qW]
  rw [e] at h
  convert h using 1
  simp only [rW, Function.comp, Pi.pow_apply]; push_cast; ring

lemma qW_zero (η : ℝ) (hη : 0 ≤ η) (h : qW η = 0) : rW η = -(1 * (1 - pW η ^ 2)) := by
  have hw := w_pos η hη
  have hw1 := w_le η hη
  have h' : Φ₁ (1 - w η) = 0 := by
    simp only [qW] at h
    rcases mul_eq_zero.1 h with h | h
    · exact h
    · exact absurd ((pow_eq_zero_iff two_ne_zero).1 h) hw.ne'
  have hL := L_pos (1 - w η) (by linarith)
  rw [Φ₁_eq] at h'
  rcases mul_eq_zero.1 h' with h'' | h''
  · rcases mul_eq_zero.1 h'' with h3 | h3
    · have : w η = 1 := by linarith
      simp only [rW, pW, Φ, Φ₁, Φ₂, this]; norm_num
    · have : w η = 1 / 2 := by linarith
      simp only [rW, pW, Φ, Φ₁, Φ₂, this]; norm_num
  · exact absurd h'' hL.ne'

lemma pW_lim : Tendsto pW atTop (𝓝 1) := by
  have hw : Tendsto w atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ 1 tendsto_id)
  have hs : Tendsto (fun η => 1 - w η) atTop (𝓝 (1 - 0)) := tendsto_const_nhds.sub hw
  have hc : Continuous Φ := by unfold Φ; fun_prop
  have := (hc.tendsto (1 - 0)).comp hs
  have e : Φ (1 - 0) = 1 := by simp only [Φ]; norm_num
  rw [e] at this
  exact this

/-- The obligation of hypothesis 3 of `fs_monotone_of_limit`, written out. -/
theorem witness : ∃ (β : ℝ) (_ : 0 < β) (_ : β ≤ 1) (f p q : ℝ → ℝ)
    (_ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (_ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - β * (1 - p η ^ 2)) (Ici 0) η)
    (_ : f 0 = 0) (_ : p 0 = 0) (_ : Tendsto p atTop (𝓝 1)) (η : ℝ) (_ : η ∈ Ici (0 : ℝ)),
    ¬ 0 < q η := by
  have q0 : qW 0 = 0 := by simp [qW, w, Φ₁]
  refine ⟨1, one_pos, le_rfl, fW, pW, qW, fun η hη => (pW_deriv η hη).hasDerivWithinAt, fun η hη => ?_,
    ?_, by simp [pW, w, Φ], pW_lim, 0, mem_Ici.2 le_rfl, by rw [q0]; exact lt_irrefl 0⟩
  · refine (qW_deriv η hη).hasDerivWithinAt.congr_deriv ?_
    by_cases h : qW η = 0
    · rw [qW_zero η hη h, h]; simp [fW, h]
    · simp only [fW]; field_simp; ring
  · simp [fW, q0]

end Scratch.FreeF
