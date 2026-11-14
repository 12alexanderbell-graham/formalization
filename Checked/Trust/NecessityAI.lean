import Checked.Trust.NecessityAD

/-! Hypothesis necessity for `FRCosmo.curv_derivs` (run 2026-11-14T2228Z): the Ricci scalar `R = −6(Ḣ + 2H²)` and
its first three time derivatives at `t₀` in terms of `H₀, q₀, j₀, s₀, l₀`, for a scale factor `C⁵` at `t₀` with
`a(t₀) > 0`, `H₀ > 0`.

* `a(t₀) > 0` (hypothesis 1) is REDUNDANT: `H₀ > 0` forces `a(t₀) ≠ 0` (Lean's `x/0 = 0`), and every quantity in
  the statement (`hubble`, `decel`, `cosmoCoeff`, `curv`) is unchanged under `a ↦ −a`, so the case `a(t₀) < 0`
  follows from the headline applied to `−a`.
* `H₀ > 0` (hypothesis 2) is NEEDED: `a = 1 + t²` at `t₀ = 0` is smooth and positive with `H₀ = 0` and Lean's
  `q₀ = 0` (division by `ȧ(0)² = 0`), while `Ḣ(0) = 2`, so `R(0) = −12` and the first formula's right side is `0`.
* smoothness (hypothesis 3) is NEEDED: `a = 1 + t + t²|t|` at `t₀ = 0` has `a(0) = 1`, `H₀ = 1`, `ä = 6|t|`, so
  `q₀ = 0` and Lean's junk third derivative gives `j₀ = 0`; the second formula's right side is
  `−6(j₀ − q₀ − 2) = 12`, while `R = −6(ä/a + ȧ²/a²)` near `0` is not differentiable at `0` (else
  `6|t| = a(−R/6 − ȧ²/a²)` would be), so Lean's `Ṙ(0)` is the junk `0`.

`FRCosmo.fR_values` (its one hypothesis, the model bundle `IsFRCosmo`, is NEEDED): with `a = 0`, `F = 0`, `Ω = 0`
every coefficient is Lean's `0` and the second identity reads `0 = −Q₂(0, 0, 0) = 32`. -/

namespace Checked.Trust.NecessityAI
open Filter Topology
open Checked.Cosmography Checked.Cosmography.Aviles Checked.Trust.NecessityAD

/-! ### Invariance under `a ↦ −a` -/

theorem hubble_neg (a : ℝ → ℝ) : hubble (fun t => -a t) = hubble a := by
  funext t; simp only [hubble, deriv.fun_neg']; rw [neg_div_neg_eq]

theorem curv_neg (a : ℝ → ℝ) : FRCosmo.curv (fun t => -a t) = FRCosmo.curv a := by
  funext t; simp only [FRCosmo.curv, hubble_neg]

theorem decel_neg (a : ℝ → ℝ) (t : ℝ) : decel (fun t => -a t) t = decel a t := by
  simp only [decel, deriv.fun_neg']; ring

theorem cosmoCoeff_neg (n : ℕ) (a : ℝ → ℝ) (t : ℝ) :
    cosmoCoeff n (fun t => -a t) t = cosmoCoeff n a t := by
  simp only [cosmoCoeff, iteratedDeriv_fun_neg, hubble_neg]
  rw [neg_mul, neg_div_neg_eq]

/-- `a(t₀) > 0` is redundant in `FRCosmo.curv_derivs`: `H₀ > 0` gives `a(t₀) ≠ 0`, and the statement is invariant
under `a ↦ −a`. -/
theorem curv_derivs_r1 : dropped% Checked.Cosmography.FRCosmo.curv_derivs 1 := by
  intro a t₀ hH hs
  rcases lt_trichotomy (a t₀) 0 with h | h | h
  · have hH' : 0 < hubble (fun t => -a t) t₀ := by rw [hubble_neg]; exact hH
    have := FRCosmo.curv_derivs (fun t => -a t) t₀ (by show 0 < -a t₀; linarith) hH' hs.neg
    simpa only [curv_neg, hubble_neg, decel_neg, cosmoCoeff_neg] using this
  · exfalso
    have : hubble a t₀ = 0 := by simp [hubble, h]
    linarith
  · exact FRCosmo.curv_derivs a t₀ h hH hs

/-! ### `H₀ > 0` -/

theorem sq_hubble : hubble (fun t : ℝ => 1 + t ^ 2) = fun t => 2 * t / (1 + t ^ 2) := by
  funext t
  have h : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * t) t := by
    simpa using (hasDerivAt_pow 2 t).const_add 1
  simp only [hubble, h.deriv]

/-- `H₀ > 0` is needed in `FRCosmo.curv_derivs`: `a = 1 + t²` at `0` has `H₀ = 0`, `Ḣ(0) = 2`, so
`R(0) = −12`, while the formula `−6H₀²(1 − q₀)` gives `0`. -/
theorem curv_derivs_h2 : necessity% Checked.Cosmography.FRCosmo.curv_derivs 2 := by
  refine ⟨fun t => 1 + t ^ 2, 0, by norm_num, ?_, ?_⟩
  · have : ContDiff ℝ 5 (fun t : ℝ => 1 + t ^ 2) := by fun_prop
    exact this.contDiffAt
  · intro h
    have h1 := h.1
    have hd : HasDerivAt (hubble (fun t : ℝ => 1 + t ^ 2)) 2 0 := by
      rw [sq_hubble]
      have e1 : HasDerivAt (fun t : ℝ => 2 * t) 2 0 := by simpa using (hasDerivAt_id (0 : ℝ)).const_mul 2
      have e2 : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * 0) 0 := by
        simpa using (hasDerivAt_pow 2 (0 : ℝ)).const_add 1
      have := e1.div e2 (by norm_num)
      convert this using 1
      norm_num
    have hH0 : hubble (fun t : ℝ => 1 + t ^ 2) 0 = 0 := by rw [sq_hubble]; simp
    simp only [FRCosmo.curv, hd.deriv, hH0] at h1
    norm_num at h1

/-! ### Smoothness -/

/-- `a = 1 + t + t²|t|`. -/
noncomputable abbrev K3 : ℝ → ℝ := G 1 1 0 0 1 1

theorem K3_d1 : deriv K3 = fun x => 1 + 3 * (x * |x|) := by
  rw [G_deriv_succ]; funext x; simp [G]

theorem K3_d1_hasDerivAt (x : ℝ) : HasDerivAt (deriv K3) (6 * |x|) x := by
  rw [K3_d1]
  have h := (G_hasDerivAt 1 0 0 0 3 0 x)
  convert h using 1
  · funext t; simp [G]
  · simp; ring

theorem K3_d2 : deriv (deriv K3) = fun x => 6 * |x| := by
  funext x; exact (K3_d1_hasDerivAt x).deriv

/-- `R = −6(ä/a + ȧ²/a²)` near `0` for `a = 1 + t + t²|t|`. -/
theorem K3_curv : ∀ᶠ t in 𝓝 0, FRCosmo.curv K3 t =
    -6 * ((6 * |t| * K3 t - deriv K3 t ^ 2) / K3 t ^ 2 + 2 * (deriv K3 t / K3 t) ^ 2) := by
  have hc : ContinuousAt K3 0 := (G_hasDerivAt 1 1 0 0 1 1 0).continuousAt
  have hne : ∀ᶠ t in 𝓝 0, K3 t ≠ 0 := hc.eventually_ne (by simp [G])
  filter_upwards [hne] with t ht
  have hda : HasDerivAt K3 (deriv K3 t) t := (G_hasDerivAt 1 1 0 0 1 1 t).differentiableAt.hasDerivAt
  have hH : HasDerivAt (hubble K3) ((6 * |t| * K3 t - deriv K3 t * deriv K3 t) / K3 t ^ 2) t := by
    have := (K3_d1_hasDerivAt t).div hda ht
    exact this
  simp only [FRCosmo.curv, hH.deriv, hubble]
  ring

theorem K3_curv_not_diff : ¬ DifferentiableAt ℝ (FRCosmo.curv K3) 0 := by
  intro h
  apply not_differentiableAt_abs_zero
  have hda : DifferentiableAt ℝ K3 0 := (G_hasDerivAt 1 1 0 0 1 1 0).differentiableAt
  have hd1 : DifferentiableAt ℝ (deriv K3) 0 := (K3_d1_hasDerivAt 0).differentiableAt
  have hK0 : K3 0 ≠ 0 := by simp [G]
  have hg : DifferentiableAt ℝ
      (fun t => K3 t * (-(FRCosmo.curv K3 t) / 6 - (deriv K3 t / K3 t) ^ 2) / 6) 0 :=
    ((hda.mul ((h.neg.div_const 6).sub ((hd1.div hda hK0).pow 2))).div_const 6)
  have hc : ContinuousAt K3 0 := hda.continuousAt
  have hne : ∀ᶠ t in 𝓝 0, K3 t ≠ 0 := hc.eventually_ne hK0
  refine hg.congr_of_eventuallyEq ?_
  filter_upwards [K3_curv, hne] with t ht hn
  rw [ht]
  field_simp
  ring

/-- Smoothness (`C⁵` at `t₀`) is needed in `FRCosmo.curv_derivs`: `a = 1 + t + t²|t|` at `0` has `a(0) = 1`,
`H₀ = 1`, `q₀ = 0` and Lean's junk `j₀ = 0`, so the second formula gives `Ṙ(0) = 12`, while `R` is not
differentiable at `0` and Lean's `Ṙ(0)` is `0`. -/
theorem curv_derivs_h3 : necessity% Checked.Cosmography.FRCosmo.curv_derivs 3 := by
  obtain ⟨h0, hH, hq, hj⟩ := G1_coeffs 0 1 (by norm_num)
  have h0' : K3 0 = 1 := h0
  have hH' : hubble K3 0 = 1 := hH
  have hq' : decel K3 0 = -(2 * 0) := hq
  have hj' : cosmoCoeff 3 K3 0 = 0 := hj
  refine ⟨K3, 0, by rw [h0']; norm_num, by rw [hH']; norm_num, ?_⟩
  intro h
  have h2 := h.2.1
  rw [deriv_zero_of_not_differentiableAt K3_curv_not_diff, hH', hq', hj'] at h2
  norm_num at h2

/-! ### `FRCosmo.fR_values` -/

/-- The model hypothesis `IsFRCosmo` is needed in `FRCosmo.fR_values`: for `a = 0`, `F = 0`, `Ω = 0` (no model)
every cosmographic coefficient is Lean's `0`, the left side of the second identity is `0` and its right side is
`−Q₂(0, 0, 0) = 32`. -/
theorem fR_values_h1 : necessity% Checked.Cosmography.FRCosmo.fR_values 1 := by
  refine ⟨0, fun _ => 0, fun _ => 0, 0, ?_⟩
  intro h
  have h2 := h.2.1
  simp [hubble, decel, Aviles.cosmoCoeff, FRCosmo.P2, FRCosmo.Q2] at h2

end Checked.Trust.NecessityAI
