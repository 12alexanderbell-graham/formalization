import Checked.Fidelity.RedshiftCoeffSpecs
import Checked.Trust.NonVacuity
import Checked.Trust.NecessityD
import Mathlib.Analysis.Calculus.Deriv.Abs

/-! Hypothesis necessity for the two pinning theorems of `redshift` and `cosmoCoeff` (trust track T1): the
physical-domain hypothesis of each pin (a positive, continuously differentiable scale factor along the ray; a
positive, smooth enough, non-stationary scale factor at the observation time) is needed. Witness: a redshift
(resp. coefficient) function that agrees with the program's definition wherever the scale factor is positive at
the emission (resp. observation) time and is shifted by one elsewhere. It obeys every law of the blind core
specification, because each law speaks only about positive scale factors there, and it differs from the
program's definition for a negative constant scale factor, where the pin's domain hypothesis fails. So the pins
say nothing outside their domain, as their statements claim. For the coefficient pin each part of the domain
hypothesis is needed on its own (a scale factor negative at the observation time; one whose derivative has a corner
there; one with zero expansion rate there); for the redshift pin the positivity part is. Run 2026-11-15T0628Z. -/

namespace Checked.Trust.NCAM

open Set Filter Topology Checked.Cosmography Checked.Cosmography.Aviles Checked.Fidelity

/-- `redshift` where the scale factor is positive at the emission time, shifted by one elsewhere. -/
noncomputable def Zj (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  if 0 < a t then redshift a t₀ t else redshift a t₀ t + 1

theorem Zj_of_pos {a : ℝ → ℝ} {t₀ t : ℝ} (h : 0 < a t) : Zj a t₀ t = redshift a t₀ t := by
  simp [Zj, h]

theorem Zj_meets : RedshiftSpecCore Zj where
  integral_law a t₀ t h := by
    rw [Zj_of_pos h.pos_left]; exact redshift_meets_core.integral_law a t₀ t h
  ratio_law a t₀ t h := by
    rw [Zj_of_pos h.pos_left]; exact redshift_meets_core.ratio_law a t₀ t h
  self_zero a t h := by
    rw [Zj_of_pos h]; exact redshift_meets_core.self_zero a t h
  compose a t t₁ t₀ h₁ h₂ := by
    simp only [Zj_of_pos h₁.pos_left, Zj_of_pos h₂.pos_left]
    exact redshift_meets_core.compose a t t₁ t₀ h₁ h₂
  rescale_invariant a c t₀ t hc h := by
    have h1 : 0 < (fun s => c * a s) t := mul_pos hc h.pos_left
    rw [Zj_of_pos (a := fun s => c * a s) (t := t) h1, Zj_of_pos h.pos_left]
    exact redshift_meets_core.rescale_invariant a c t₀ t hc h
  time_translate a τ t₀ t h := by
    have h1 : 0 < (fun s => a (s + τ)) t := h.pos_left
    rw [Zj_of_pos (a := fun s => a (s + τ)) (t := t) h1, Zj_of_pos (a := a) (t := t + τ) h.pos_left]
    exact redshift_meets_core.time_translate a τ t₀ t h
  local_dep a b t₀ t h hab := by
    have hb : 0 < b t := by rw [← hab (left_mem_uIcc : t ∈ uIcc t t₀)]; exact h.pos_left
    rw [Zj_of_pos hb, Zj_of_pos h.pos_left]
    exact redshift_meets_core.local_dep a b t₀ t h hab
  expanding_pos a t₀ t htt h hd := by
    rw [Zj_of_pos h.pos_left]; exact redshift_meets_core.expanding_pos a t₀ t htt h hd
  de_sitter A h t₀ t hA := by
    have h1 : 0 < (fun s => A * Real.exp (h * s)) t := mul_pos hA (Real.exp_pos _)
    rw [Zj_of_pos (a := fun s => A * Real.exp (h * s)) (t := t) h1]; exact redshift_meets_core.de_sitter A h t₀ t hA
  power_law p t₀ t ht ht₀ := by
    have h1 : 0 < (fun s : ℝ => s ^ p) t := Real.rpow_pos_of_pos ht p
    rw [Zj_of_pos (a := fun s : ℝ => s ^ p) (t := t) h1]; exact redshift_meets_core.power_law p t₀ t ht ht₀
  milne t₀ t ht ht₀ := by
    have h1 : 0 < (fun s : ℝ => s) t := ht
    rw [Zj_of_pos (a := fun s : ℝ => s) (t := t) h1]; exact redshift_meets_core.milne t₀ t ht ht₀
  static A t₀ t hA := by
    have h1 : 0 < (fun _ : ℝ => A) t := hA
    rw [Zj_of_pos (a := fun _ : ℝ => A) (t := t) h1]; exact redshift_meets_core.static A t₀ t hA
  not_linear_hubble := by
    have h1 : 0 < (fun s : ℝ => Real.exp s) 0 := Real.exp_pos 0
    rw [Zj_of_pos (a := fun s : ℝ => Real.exp s) (t := 0) h1]; exact redshift_meets_core.not_linear_hubble
  not_inverted := by
    have h1 : 0 < (fun s : ℝ => Real.exp s) 0 := Real.exp_pos 0
    rw [Zj_of_pos (a := fun s : ℝ => Real.exp s) (t := 0) h1]; exact redshift_meets_core.not_inverted

/-- The ray hypothesis (positive, continuously differentiable scale factor between emission and observation) is
needed in `redshiftCore_pins`: a function obeying every law of the core specification but shifted by one where
the scale factor is not positive differs from `redshift` for a negative constant scale factor. -/
theorem redshiftCore_pins_h2 : necessity% Checked.Fidelity.redshiftCore_pins 2 :=
  ⟨Zj, Zj_meets, fun _ => -1, 0, 0, by simp [Zj]⟩

open Classical in
/-- `cosmoCoeff` where the scale factor meets the domain hypothesis of the pin (positive, smooth enough,
non-stationary), shifted by one elsewhere. -/
noncomputable def Ck (n : ℕ) (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  if CoeffOK n a t then cosmoCoeff n a t else cosmoCoeff n a t + 1

theorem Ck_of {n : ℕ} {a : ℝ → ℝ} {t : ℝ} (h : CoeffOK n a t) : Ck n a t = cosmoCoeff n a t := by
  simp [Ck, h]

theorem rpow_ok (n : ℕ) (p t : ℝ) (ht : 0 < t) (hp : p ≠ 0) : CoeffOK n (fun s : ℝ => s ^ p) t := by
  refine ⟨Real.rpow_pos_of_pos ht p, Real.contDiffAt_rpow_const_of_ne ht.ne', ?_⟩
  rw [Real.deriv_rpow_const t p]
  exact mul_ne_zero hp (Real.rpow_pos_of_pos ht _).ne'

theorem dS_ok (n : ℕ) (A h t : ℝ) (hA : 0 < A) (hh : h ≠ 0) :
    CoeffOK n (fun s => A * Real.exp (h * s)) t := by
  refine ⟨mul_pos hA (Real.exp_pos _), by fun_prop, ?_⟩
  have h1 : deriv (fun s => A * Real.exp (h * s)) t = A * (h * Real.exp (h * t)) := by
    have := iteratedDeriv_dS 1 A h t
    simpa [iteratedDeriv_one] using this
  rw [h1]; exact mul_ne_zero hA.ne' (mul_ne_zero hh (Real.exp_pos _).ne')

theorem Ck_meets : CosmoCoeffSpecCore Ck where
  defining n a t h := by rw [Ck_of h]; exact cosmoCoeff_meets_core.defining n a t h
  taylor_law n a t₀ h := by
    have e : (fun Δ : ℝ => a (t₀ + Δ) / a t₀ - ∑ k ∈ Finset.range (n + 1),
        Ck k a t₀ * (deriv a t₀ / a t₀ * Δ) ^ k / (k.factorial : ℝ)) =
        (fun Δ : ℝ => a (t₀ + Δ) / a t₀ - ∑ k ∈ Finset.range (n + 1),
        cosmoCoeff k a t₀ * (deriv a t₀ / a t₀ * Δ) ^ k / (k.factorial : ℝ)) := by
      funext Δ
      congr 1
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [Ck_of ⟨h.1, h.2.1.of_le (by exact_mod_cast hk'), h.2.2⟩]
    rw [e]; exact cosmoCoeff_meets_core.taylor_law n a t₀ h
  zero a t h := by rw [Ck_of h]; exact cosmoCoeff_meets_core.zero a t h
  one a t h := by rw [Ck_of h]; exact cosmoCoeff_meets_core.one a t h
  rescale_invariant n a c t hc h := by
    have h1 : CoeffOK n (fun s => c * a s) t := by
      refine ⟨mul_pos hc h.1, contDiffAt_const.mul h.2.1, ?_⟩
      rw [deriv_const_mul_field']; exact mul_ne_zero hc.ne' h.2.2
    rw [Ck_of h1, Ck_of h]
    exact cosmoCoeff_meets_core.rescale_invariant n a c t hc h
  time_translate n a τ t h := by
    have h1 : CoeffOK n (fun s => a (s + τ)) t := by
      refine ⟨h.1, h.2.1.comp t (contDiffAt_id.add contDiffAt_const), ?_⟩
      rw [deriv_comp_add_const]; exact h.2.2
    rw [Ck_of h1, Ck_of (a := a) (t := t + τ) h]
    exact cosmoCoeff_meets_core.time_translate n a τ t h
  de_sitter n A h t hA hh := by
    rw [Ck_of (dS_ok n A h t hA hh)]; exact cosmoCoeff_meets_core.de_sitter n A h t hA hh
  power_law n p t ht hp := by
    rw [Ck_of (rpow_ok n p t ht hp)]; exact cosmoCoeff_meets_core.power_law n p t ht hp
  milne n t ht hn := by
    have h1 : CoeffOK n (fun s : ℝ => s) t := ⟨ht, contDiffAt_id, by simp⟩
    rw [Ck_of h1]; exact cosmoCoeff_meets_core.milne n t ht hn
  matter_q t ht := by
    rw [Ck_of (rpow_ok 2 _ t ht (by norm_num))]; exact cosmoCoeff_meets_core.matter_q t ht
  matter_j t ht := by
    rw [Ck_of (rpow_ok 3 _ t ht (by norm_num))]; exact cosmoCoeff_meets_core.matter_j t ht
  not_q_sign := by
    rw [Ck_of (rpow_ok 2 _ 1 one_pos (by norm_num))]; exact cosmoCoeff_meets_core.not_q_sign
  not_unnormalized := by
    have e : (fun s : ℝ => Real.exp (2 * s)) = fun s => 1 * Real.exp (2 * s) := by funext s; ring
    have h1 := dS_ok 2 1 2 0 one_pos two_ne_zero
    rw [← e] at h1
    rw [Ck_of h1]; exact cosmoCoeff_meets_core.not_unnormalized

/-- `1 + t + t|t|` is not twice continuously differentiable at `0` (its derivative `1 + 2|t|` has a corner). -/
theorem kink0_not_C2 : ¬ ContDiffAt ℝ 2 (Checked.Trust.NCD.kink 0) 0 := by
  intro h
  rw [show (2 : WithTop ℕ∞) = ((1 : ℕ) + 1 : ℕ) by rfl] at h
  obtain ⟨f', ⟨u, hu, hf⟩, hc⟩ := contDiffAt_succ_iff_hasFDerivAt.1 h
  have hd : DifferentiableAt ℝ f' 0 := hc.differentiableAt (by norm_num)
  have hd1 : DifferentiableAt ℝ (fun y => f' y 1) 0 := hd.clm_apply (differentiableAt_const 1)
  apply not_differentiableAt_abs_zero
  have e : ∀ᶠ y in 𝓝 (0 : ℝ), |y| = (f' y 1 - 1) / 2 := by
    filter_upwards [hu] with y hy
    have h1 := (hf y hy).hasDerivAt
    have h2 := Checked.Trust.NCD.kink_hasDerivAt 0 y
    have := h1.unique h2
    simp only [pow_zero, one_mul, Nat.cast_zero, zero_add] at this
    linarith
  exact ((hd1.sub_const 1).div_const 2).congr_of_eventuallyEq e

/-- The domain hypothesis (positive, smooth enough, non-stationary scale factor at the observation time) is
needed in `cosmoCoeffCore_pins`: a function obeying every law of the core specification but shifted by one
outside that domain differs from `cosmoCoeff` for a negative constant scale factor. -/
theorem cosmoCoeffCore_pins_h2 : necessity% Checked.Fidelity.cosmoCoeffCore_pins 2 :=
  ⟨Ck, Ck_meets, 0, fun _ => -1, 0, by simp [Ck, CoeffOK]⟩

/-- Positivity of the scale factor is needed in `cosmoCoeffCore_pins` (the other two parts kept): `t − 1` at `0`. -/
theorem cosmoCoeffCore_pins_p2_1 : necessity% Checked.Fidelity.cosmoCoeffCore_pins 2 1 := by
  refine ⟨Ck, Ck_meets, 0, fun s => s - 1, 0, ⟨by fun_prop, ?_⟩, by norm_num [Ck, CoeffOK]⟩
  have : deriv (fun s : ℝ => s - 1) 0 = 1 := by
    rw [deriv_sub_const]; simp
  rw [this]; norm_num

/-- Smoothness of the scale factor is needed in `cosmoCoeffCore_pins` (the other two parts kept):
`1 + t + t|t|` at `0` for the second coefficient. -/
theorem cosmoCoeffCore_pins_p2_2 : necessity% Checked.Fidelity.cosmoCoeffCore_pins 2 2 := by
  have hd : deriv (Checked.Trust.NCD.kink 0) 0 = 1 := by
    rw [(Checked.Trust.NCD.kink_hasDerivAt 0 0).deriv]; simp
  refine ⟨Ck, Ck_meets, 2, Checked.Trust.NCD.kink 0, 0, ⟨by simp [Checked.Trust.NCD.kink], by rw [hd]; norm_num⟩, ?_⟩
  simp [Ck, CoeffOK, kink0_not_C2]

/-- A nonzero expansion rate is needed in `cosmoCoeffCore_pins` (the other two parts kept): `1 + t²` at `0`. -/
theorem cosmoCoeffCore_pins_p2_3 : necessity% Checked.Fidelity.cosmoCoeffCore_pins 2 3 := by
  have hd : deriv (fun s : ℝ => 1 + s ^ 2) 0 = 0 := by
    rw [((hasDerivAt_pow 2 (0 : ℝ)).const_add 1).deriv]; simp
  refine ⟨Ck, Ck_meets, 0, fun s => 1 + s ^ 2, 0, ⟨by norm_num, by fun_prop⟩, ?_⟩
  simp [Ck, CoeffOK, hd]

/-- Positivity of the scale factor along the ray is needed in `redshiftCore_pins` (continuous differentiability
kept): a negative constant scale factor. -/
theorem redshiftCore_pins_p2_1 : necessity% Checked.Fidelity.redshiftCore_pins 2 1 :=
  ⟨Zj, Zj_meets, fun _ => -1, 0, 0, ⟨fun _ _ => trivial, contDiffOn_const⟩, by simp [Zj]⟩

end Checked.Trust.NCAM
