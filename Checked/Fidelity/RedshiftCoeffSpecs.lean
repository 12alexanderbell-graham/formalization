import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Checked.Cosmography.LCDMCoefficients

/-!
# `redshift` and `cosmoCoeff` pinned by blind textbook specifications (trust track T1)

The trust map (`TRUST_MAP.md`, run 2028Z) showed that the most-used unpinned physics
definitions behind the headline theorems are `Aviles.cosmoCoeff` (67 of 88 headlines) and
`redshift` (58). This file pins both.

Specifications: `Work/Fidelity/BlindSpecsZC.lean` (frozen in commit 7c6bcb7), written by a
subagent that did not read any repository definition. Here we copy, **verbatim**, the fields we
prove the definitions satisfy (`RedshiftSpecCore`, `CosmoCoeffSpecCore`). Fields of the blind
specs not yet proved for the definitions (left for a later run, listed in each structure's
docstring) are omitted; omitting fields never helps a wrong definition pass, it only removes
cross-checks.

* `redshift_meets_core`, `redshiftCore_pins`: any `Z` obeying the **integrated
  wavelength-stretching law** `1 + z = exp ∫_t^{t₀} H` equals `redshift` wherever `a > 0` is `C¹`
  on the ray's time span (the pin uses only this law, not the blind spec's ratio law).
* `cosmoCoeff_meets_core`, `cosmoCoeffCore_pins`: any `C` obeying the **cosmographic Taylor
  law** `a(t₀+Δ)/a(t₀) = Σ_{k≤n} C_k (H₀Δ)^k/k! + o(Δⁿ)` equals `cosmoCoeff` wherever `a > 0`,
  `a` is `Cⁿ` near `t₀` and `ȧ(t₀) ≠ 0` (the pin uses only this law and uniqueness of Taylor
  coefficients, `poly_littleO_coeff_zero`; not the blind spec's defining formula).
-/

namespace Checked.Fidelity

open Set Filter Asymptotics intervalIntegral Topology
open Checked.Cosmography Checked.Cosmography.Aviles

/-! ## Redshift -/

/-- (Verbatim from the blind spec.) Physical hypotheses for a light ray between times `t` and
`t₀`: the scale factor is positive and continuously differentiable on the closed interval between
them. -/
def RayOK (a : ℝ → ℝ) (t t₀ : ℝ) : Prop :=
  (∀ s ∈ uIcc t t₀, 0 < a s) ∧ ContDiffOn ℝ 1 a (uIcc t t₀)

/-- The fields of the blind `RedshiftSpec` proved below (verbatim). Not yet proved for
`redshift` (omitted): `deriv_emission`, `deriv_observation`, `low_z`. -/
structure RedshiftSpecCore (Z : (ℝ → ℝ) → ℝ → ℝ → ℝ) : Prop where
  /-- **General (pinning) law: integrated wavelength stretching.** Along a radial null ray
  `dλ/λ = (ȧ/a) dt`, hence `1 + z = λ_obs/λ_em = exp ∫_t^{t₀} H(s) ds`.
  [Peebles §5; Weinberg §1.2; Ryden §3.5]. -/
  integral_law : ∀ (a : ℝ → ℝ) (t₀ t : ℝ), RayOK a t t₀ →
    1 + Z a t₀ t = Real.exp (∫ s in t..t₀, deriv a s / a s)
  /-- **Ratio law** `1 + z = a(t₀)/a(t)` [Ryden eq. 3.46; Weinberg eq. 1.2.4]. -/
  ratio_law : ∀ (a : ℝ → ℝ) (t₀ t : ℝ), RayOK a t t₀ →
    1 + Z a t₀ t = a t₀ / a t
  /-- No redshift when emission and observation coincide. -/
  self_zero : ∀ (a : ℝ → ℝ) (t : ℝ), 0 < a t → Z a t t = 0
  /-- **Composition**: redshift factors multiply along a ray passing an intermediate
  observer at `t₁` [Weinberg §1.2]. -/
  compose : ∀ (a : ℝ → ℝ) (t t₁ t₀ : ℝ), RayOK a t t₁ → RayOK a t₁ t₀ →
    1 + Z a t₀ t = (1 + Z a t₀ t₁) * (1 + Z a t₁ t)
  /-- **Normalization invariance**: only ratios of the scale factor are physical, so
  `a ↦ c·a` (`c > 0`) leaves `z` unchanged [Ryden §3.5]. -/
  rescale_invariant : ∀ (a : ℝ → ℝ) (c t₀ t : ℝ), 0 < c → RayOK a t t₀ →
    Z (fun s => c * a s) t₀ t = Z a t₀ t
  /-- **Time-translation covariance** (choice of time origin is unphysical). -/
  time_translate : ∀ (a : ℝ → ℝ) (τ t₀ t : ℝ), RayOK a (t + τ) (t₀ + τ) →
    Z (fun s => a (s + τ)) t₀ t = Z a (t₀ + τ) (t + τ)
  /-- **Locality**: `z` depends only on the scale factor along the ray. -/
  local_dep : ∀ (a b : ℝ → ℝ) (t₀ t : ℝ), RayOK a t t₀ → EqOn a b (uIcc t t₀) →
    Z b t₀ t = Z a t₀ t
  /-- **Expanding universe ⇒ redshift** (`z > 0` for past emission when `ȧ > 0`). -/
  expanding_pos : ∀ (a : ℝ → ℝ) (t₀ t : ℝ), t < t₀ → RayOK a t t₀ →
    (∀ s ∈ Ioo t t₀, 0 < deriv a s) → 0 < Z a t₀ t
  /-- **Anchor: de Sitter** `a = A e^{ht}`: `1 + z = e^{h(t₀-t)}`. -/
  de_sitter : ∀ (A h t₀ t : ℝ), 0 < A →
    Z (fun s => A * Real.exp (h * s)) t₀ t = Real.exp (h * (t₀ - t)) - 1
  /-- **Anchor: power law** `a = t^p` (e.g. matter `p = 2/3`, radiation `p = 1/2`),
  for positive times: `1 + z = (t₀/t)^p`. -/
  power_law : ∀ (p t₀ t : ℝ), 0 < t → 0 < t₀ →
    Z (fun s => s ^ p) t₀ t = t₀ ^ p / t ^ p - 1
  /-- **Anchor: Milne** `a = t`: `1 + z = t₀/t`. -/
  milne : ∀ (t₀ t : ℝ), 0 < t → 0 < t₀ → Z (fun s => s) t₀ t = t₀ / t - 1
  /-- **Anchor: static universe** `a = A`: no cosmological redshift. -/
  static : ∀ (A t₀ t : ℝ), 0 < A → Z (fun _ => A) t₀ t = 0
  /-- **Near-miss negative**: the linear Hubble law `z = H₀(t₀ - t)` is not exact
  (de Sitter, `h = 1`, `t₀ - t = 1`: true `z = e - 1`, not `1`). -/
  not_linear_hubble : Z (fun s => Real.exp s) 1 0 ≠ 1
  /-- **Near-miss negative**: the ratio is not inverted (`z ≠ a(t)/a(t₀) - 1`). -/
  not_inverted : Z (fun s => Real.exp s) 1 0 ≠ Real.exp (-1) - 1

/-- FTC for `log a` on an ordered interval. -/
lemma integral_logDeriv_of_le {a : ℝ → ℝ} {u v : ℝ} (huv : u ≤ v) (hpos : ∀ s ∈ Icc u v, 0 < a s)
    (hcd : ContDiffOn ℝ 1 a (Icc u v)) :
    ∫ s in u..v, deriv a s / a s = Real.log (a v) - Real.log (a u) := by
  rcases huv.lt_or_eq with huv | rfl
  · have hcont : ContinuousOn a (Icc u v) := hcd.continuousOn
    have hdiff : ∀ x ∈ Ioo u v, HasDerivAt a (deriv a x) x := fun x hx =>
      ((hcd.contDiffAt (Icc_mem_nhds hx.1 hx.2)).differentiableAt (by norm_num)).hasDerivAt
    apply integral_eq_sub_of_hasDerivAt_of_le huv.le
    · exact fun x hx => (hcont x hx).log (hpos x hx).ne'
    · intro x hx
      exact (hdiff x hx).log (hpos x ⟨hx.1.le, hx.2.le⟩).ne'
    · -- integrable: equals the continuous `derivWithin a (Icc u v) / a` on `Ioo u v`
      have hc' : ContinuousOn (fun s => derivWithin a (Icc u v) s / a s) (Icc u v) :=
        (hcd.continuousOn_derivWithin (uniqueDiffOn_Icc huv) le_rfl).div hcont
          (fun x hx => (hpos x hx).ne')
      have hi := hc'.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) huv.le
      refine hi.congr_uIoo (fun x hx => ?_)
      rw [uIoo_of_le huv.le] at hx
      simp only
      rw [derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
  · simp

lemma integral_logDeriv {a : ℝ → ℝ} {t₀ t : ℝ} (h : RayOK a t t₀) :
    ∫ s in t..t₀, deriv a s / a s = Real.log (a t₀) - Real.log (a t) := by
  obtain ⟨hpos, hcd⟩ := h
  rcases le_total t t₀ with hle | hle
  · rw [uIcc_of_le hle] at hpos hcd
    exact integral_logDeriv_of_le hle hpos hcd
  · rw [uIcc_of_ge hle] at hpos hcd
    rw [integral_symm, integral_logDeriv_of_le hle hpos hcd]; ring

lemma RayOK.pos_left {a : ℝ → ℝ} {t t₀ : ℝ} (h : RayOK a t t₀) : 0 < a t :=
  h.1 t left_mem_uIcc

lemma RayOK.pos_right {a : ℝ → ℝ} {t t₀ : ℝ} (h : RayOK a t t₀) : 0 < a t₀ :=
  h.1 t₀ right_mem_uIcc

lemma redshift_integral_law (a : ℝ → ℝ) (t₀ t : ℝ) (h : RayOK a t t₀) :
    1 + redshift a t₀ t = Real.exp (∫ s in t..t₀, deriv a s / a s) := by
  rw [integral_logDeriv h, Real.exp_sub, Real.exp_log h.pos_right, Real.exp_log h.pos_left]
  simp [redshift]

theorem redshift_meets_core : RedshiftSpecCore redshift where
  integral_law := redshift_integral_law
  ratio_law a t₀ t _ := by simp [redshift]
  self_zero a t h := by simp [redshift, h.ne']
  compose a t t₁ t₀ h₁ h₂ := by
    have := h₁.pos_right.ne'
    simp only [redshift, add_sub_cancel]
    field_simp
  rescale_invariant a c t₀ t hc _ := by
    simp only [redshift]; rw [mul_div_mul_left _ _ hc.ne']
  time_translate a τ t₀ t _ := rfl
  local_dep a b t₀ t _ hab := by
    simp only [redshift, hab (left_mem_uIcc : t ∈ uIcc t t₀),
      hab (right_mem_uIcc : t₀ ∈ uIcc t t₀)]
  expanding_pos a t₀ t htt h hd := by
    obtain ⟨hpos, hcd⟩ := h
    rw [uIcc_of_le htt.le] at hpos hcd
    have hmono : StrictMonoOn a (Icc t t₀) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc t t₀) hcd.continuousOn
      intro x hx
      rw [interior_Icc] at hx
      exact hd x hx
    have hlt : a t < a t₀ := hmono (left_mem_Icc.2 htt.le) (right_mem_Icc.2 htt.le) htt
    have ht : 0 < a t := hpos t (left_mem_Icc.2 htt.le)
    simp only [redshift, sub_pos]
    rw [one_lt_div ht]; exact hlt
  de_sitter A h t₀ t hA := by
    simp only [redshift]
    rw [mul_div_mul_left _ _ hA.ne', ← Real.exp_sub]; ring_nf
  power_law p t₀ t ht ht₀ := rfl
  milne t₀ t ht ht₀ := rfl
  static A t₀ t hA := by simp [redshift, hA.ne']
  not_linear_hubble := by
    simp only [redshift, Real.exp_zero, div_one]
    intro h
    have := Real.add_one_lt_exp (one_ne_zero (α := ℝ)); linarith
  not_inverted := by
    simp only [redshift, Real.exp_zero, div_one]
    intro h
    have h1 : Real.exp 1 = Real.exp (-1) := by linarith
    have := Real.exp_lt_exp.2 (show (-1 : ℝ) < 1 by norm_num); linarith

/-- **Pinning:** every `Z` obeying the integrated wavelength-stretching law equals `redshift`
on every ray along which `a > 0` is `C¹`. -/
theorem redshiftCore_pins (Z : (ℝ → ℝ) → ℝ → ℝ → ℝ) (h : RedshiftSpecCore Z) (a : ℝ → ℝ)
    (t₀ t : ℝ) (hr : RayOK a t t₀) : Z a t₀ t = redshift a t₀ t := by
  have h1 := h.integral_law a t₀ t hr
  have h2 := redshift_integral_law a t₀ t hr
  linarith

/-! ## Cosmographic coefficients -/

/-- (Verbatim from the blind spec.) Physical hypotheses for the `n`-th cosmographic coefficient
at `t`. -/
def CoeffOK (n : ℕ) (a : ℝ → ℝ) (t : ℝ) : Prop :=
  0 < a t ∧ ContDiffAt ℝ n a t ∧ deriv a t ≠ 0

/-- The fields of the blind `CosmoCoeffSpec` proved below (verbatim). Not yet proved for
`cosmoCoeff` (omitted): `decel_hubble`, `recursion`, `time_scale`. -/
structure CosmoCoeffSpecCore (C : ℕ → (ℝ → ℝ) → ℝ → ℝ) : Prop where
  /-- **Defining formula** `C n = a⁽ⁿ⁾ / (a Hⁿ)`, `H = ȧ/a`
  [Visser eqs. (1)–(5); Aviles et al. §II]. -/
  defining : ∀ (n : ℕ) (a : ℝ → ℝ) (t : ℝ), CoeffOK n a t →
    C n a t = iteratedDeriv n a t / (a t * (deriv a t / a t) ^ n)
  /-- **General (pinning) law: cosmographic Taylor series** of the scale factor,
  `a(t₀+Δ)/a(t₀) = Σ_{k=0}^{n} C k · (H₀Δ)^k / k! + o(Δⁿ)`, valid when `a` is `C^n` near
  `t₀` (Peano remainder) [Visser eq. (6); Aviles et al. eq. (2)]. -/
  taylor_law : ∀ (n : ℕ) (a : ℝ → ℝ) (t₀ : ℝ), CoeffOK n a t₀ →
    (fun Δ : ℝ => a (t₀ + Δ) / a t₀ -
        ∑ k ∈ Finset.range (n + 1),
          C k a t₀ * (deriv a t₀ / a t₀ * Δ) ^ k / (k.factorial : ℝ))
      =o[nhds 0] (fun Δ : ℝ => Δ ^ n)
  /-- `C 0 = 1` (normalization by `a`). -/
  zero : ∀ (a : ℝ → ℝ) (t : ℝ), CoeffOK 0 a t → C 0 a t = 1
  /-- `C 1 = ȧ/(aH) = 1`. -/
  one : ∀ (a : ℝ → ℝ) (t : ℝ), CoeffOK 1 a t → C 1 a t = 1
  /-- **Normalization invariance**: `a ↦ c·a` (`c > 0`) leaves every `C n` unchanged. -/
  rescale_invariant : ∀ (n : ℕ) (a : ℝ → ℝ) (c t : ℝ), 0 < c → CoeffOK n a t →
    C n (fun s => c * a s) t = C n a t
  /-- **Time-translation covariance**. -/
  time_translate : ∀ (n : ℕ) (a : ℝ → ℝ) (τ t : ℝ), CoeffOK n a (t + τ) →
    C n (fun s => a (s + τ)) t = C n a (t + τ)
  /-- **Anchor: de Sitter** `a = A e^{ht}`, `h ≠ 0`: `q = -1`, `j = s = … = 1`,
  i.e. `C n = 1` for all `n` [Visser §3]. -/
  de_sitter : ∀ (n : ℕ) (A h t : ℝ), 0 < A → h ≠ 0 →
    C n (fun s => A * Real.exp (h * s)) t = 1
  /-- **Anchor: power law** `a = t^p`, `t > 0`, `p ≠ 0`:
  `C n = p(p-1)⋯(p-n+1)/pⁿ` (matter `p = 2/3`: `q = 1/2`, `j = 1`;
  radiation `p = 1/2`: `q = 1`). -/
  power_law : ∀ (n : ℕ) (p t : ℝ), 0 < t → p ≠ 0 →
    C n (fun s => s ^ p) t = (∏ i ∈ Finset.range n, (p - (i : ℝ))) / p ^ n
  /-- **Anchor: Milne** `a = t`: coasting, `q = j = s = … = 0` (`C n = 0` for `n ≥ 2`). -/
  milne : ∀ (n : ℕ) (t : ℝ), 0 < t → 2 ≤ n → C n (fun s => s) t = 0
  /-- **Anchor: matter domination** `a ∝ t^{2/3}`: deceleration `q = 1/2`, jerk `j = 1`. -/
  matter_q : ∀ (t : ℝ), 0 < t → C 2 (fun s => s ^ (2 / 3 : ℝ)) t = -1 / 2
  matter_j : ∀ (t : ℝ), 0 < t → C 3 (fun s => s ^ (2 / 3 : ℝ)) t = 1
  /-- **Near-miss negative (sign)**: `C 2` is `-q`, not `q` (matter: `q = 1/2`). -/
  not_q_sign : C 2 (fun s => s ^ (2 / 3 : ℝ)) 1 ≠ 1 / 2
  /-- **Near-miss negative (normalization)**: `C 2` is not the unnormalized `ä/a`
  (de Sitter `h = 2`: `ä/a = 4`, but `C 2 = 1`). -/
  not_unnormalized : C 2 (fun s => Real.exp (2 * s)) 0 ≠ 4

/-- Uniqueness of Taylor coefficients: a polynomial of degree `≤ n` that is `o(Δⁿ)` at `0`
(punctured) is zero. -/
theorem poly_littleO_coeff_zero (n : ℕ) (c : ℕ → ℝ)
    (h : (fun Δ : ℝ => ∑ k ∈ Finset.range (n + 1), c k * Δ ^ k) =o[𝓝[≠] 0] fun Δ => Δ ^ n) :
    ∀ k ≤ n, c k = 0 := by
  induction n generalizing c with
  | zero =>
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [zero_add, Finset.sum_range_one, pow_zero, mul_one] at h
    have h1 := (isLittleO_one_iff ℝ).1 h
    have h2 : Tendsto (fun _ : ℝ => c 0) (𝓝[≠] 0) (𝓝 (c 0)) := tendsto_const_nhds
    exact tendsto_nhds_unique h2 h1
  | succ n ih =>
    -- `c 0 = 0`
    have hS : Continuous (fun Δ : ℝ => ∑ k ∈ Finset.range (n + 2), c k * Δ ^ k) := by fun_prop
    have hS0 : (fun Δ : ℝ => ∑ k ∈ Finset.range (n + 2), c k * Δ ^ k) 0 = c 0 := by
      simp [Finset.sum_range_succ']
    have hlim1 : Tendsto (fun Δ : ℝ => ∑ k ∈ Finset.range (n + 2), c k * Δ ^ k) (𝓝[≠] 0)
        (𝓝 (c 0)) := by
      rw [← hS0]; exact (hS.tendsto 0).mono_left nhdsWithin_le_nhds
    have hg : (fun Δ : ℝ => Δ ^ (n + 1)) =O[𝓝[≠] 0] (fun _ => (1 : ℝ)) :=
      (((continuous_pow (n + 1)).tendsto 0).mono_left nhdsWithin_le_nhds).isBigO_one ℝ
    have hlim2 := (isLittleO_one_iff ℝ).1 (h.trans_isBigO hg)
    have hc0 : c 0 = 0 := tendsto_nhds_unique hlim1 hlim2
    -- divide by `Δ`
    have hT : (fun Δ : ℝ => ∑ k ∈ Finset.range (n + 1), c (k + 1) * Δ ^ k)
        =o[𝓝[≠] 0] fun Δ => Δ ^ n := by
      have h' := h.mul_isBigO (isBigO_refl (fun Δ : ℝ => Δ⁻¹) (𝓝[≠] 0))
      refine h'.congr' ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with Δ (hΔ : Δ ≠ 0)
        rw [Finset.sum_range_succ', hc0]
        simp only [zero_mul, add_zero, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [pow_succ, mul_assoc, mul_assoc, mul_inv_cancel₀ hΔ, mul_one]
      · filter_upwards [self_mem_nhdsWithin] with Δ (hΔ : Δ ≠ 0)
        rw [pow_succ, mul_assoc, mul_inv_cancel₀ hΔ, mul_one]
    have ih' := ih (fun k => c (k + 1)) hT
    intro k hk
    rcases k with _ | k
    · exact hc0
    · exact ih' k (by omega)

lemma cc_hubble_eq (a : ℝ → ℝ) (t : ℝ) : hubble a t = deriv a t / a t := rfl

lemma iteratedDeriv_eq_cc {n : ℕ} {a : ℝ → ℝ} {t : ℝ} (ha : a t ≠ 0) (hd : deriv a t ≠ 0) :
    iteratedDeriv n a t = cosmoCoeff n a t * (a t * (deriv a t / a t) ^ n) := by
  simp only [cosmoCoeff, cc_hubble_eq]
  rw [div_mul_cancel₀]
  exact mul_ne_zero ha (pow_ne_zero _ (div_ne_zero hd ha))

lemma cosmoCoeff_taylor_law (n : ℕ) (a : ℝ → ℝ) (t₀ : ℝ) (h : CoeffOK n a t₀) :
    (fun Δ : ℝ => a (t₀ + Δ) / a t₀ -
        ∑ k ∈ Finset.range (n + 1),
          cosmoCoeff k a t₀ * (deriv a t₀ / a t₀ * Δ) ^ k / (k.factorial : ℝ))
      =o[nhds 0] (fun Δ : ℝ => Δ ^ n) := by
  obtain ⟨ha, hcd, hd⟩ := h
  obtain ⟨U, hU, hcU⟩ := hcd.contDiffOn le_rfl (by simp)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hU
  have hopen : IsOpen (Metric.ball t₀ δ) := Metric.isOpen_ball
  have hmem : t₀ ∈ Metric.ball t₀ δ := Metric.mem_ball_self hδ
  have hT := taylor_isLittleO (convex_ball t₀ δ) hmem (hcU.mono hball)
  rw [hopen.nhdsWithin_eq hmem] at hT
  have hid : ∀ k, iteratedDerivWithin k a (Metric.ball t₀ δ) t₀ = iteratedDeriv k a t₀ :=
    fun k => iteratedDerivWithin_of_isOpen hopen hmem
  have hpoly : ∀ Δ, taylorWithinEval a n (Metric.ball t₀ δ) t₀ (t₀ + Δ) = a t₀ *
      ∑ k ∈ Finset.range (n + 1),
        cosmoCoeff k a t₀ * (deriv a t₀ / a t₀ * Δ) ^ k / (k.factorial : ℝ) := by
    intro Δ
    rw [taylor_within_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hid, iteratedDeriv_eq_cc ha.ne' hd, smul_eq_mul, add_sub_cancel_left]
    field_simp
    ring
  have hshift : Tendsto (fun Δ : ℝ => t₀ + Δ) (𝓝 0) (𝓝 t₀) := by
    simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).const_add t₀
  have h2 := (hT.comp_tendsto hshift).const_mul_left (a t₀)⁻¹
  refine h2.congr' (Eventually.of_forall fun Δ => ?_) (Eventually.of_forall fun Δ => ?_)
  · simp only [Function.comp, hpoly]
    field_simp
  · simp

lemma iteratedDeriv_milne (m : ℕ) (t : ℝ) : iteratedDeriv (m + 2) (fun s : ℝ => s) t = 0 := by
  rw [show m + 2 = (m + 1) + 1 by ring, iteratedDeriv_succ']
  have : deriv (fun s : ℝ => s) = fun _ => 1 := by funext x; simp
  rw [this, iteratedDeriv_const]; simp

lemma iteratedDeriv_rpow (n : ℕ) (p t : ℝ) :
    iteratedDeriv n (fun s : ℝ => s ^ p) t = (∏ i ∈ Finset.range n, (p - (i : ℝ))) * t ^ (p - n) := by
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const, descPochhammer_eval_eq_prod_range]

lemma iteratedDeriv_dS (n : ℕ) (A h t : ℝ) :
    iteratedDeriv n (fun s => A * Real.exp (h * s)) t = A * (h ^ n * Real.exp (h * t)) := by
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_exp_const_mul]

lemma cosmoCoeff_powerLaw (n : ℕ) (p t : ℝ) (ht : 0 < t) (hp : p ≠ 0) :
    cosmoCoeff n (fun s => s ^ p) t = (∏ i ∈ Finset.range n, (p - (i : ℝ))) / p ^ n := by
  have h1 : deriv (fun s : ℝ => s ^ p) t = p * t ^ (p - 1) := by
    have := iteratedDeriv_rpow 1 p t
    simpa [iteratedDeriv_one] using this
  have htp : 0 < t ^ p := Real.rpow_pos_of_pos ht p
  simp only [cosmoCoeff, cc_hubble_eq, h1, iteratedDeriv_rpow]
  rw [Real.rpow_sub ht, Real.rpow_sub ht, Real.rpow_natCast, Real.rpow_one]
  field_simp
  rw [div_pow]
  field_simp

theorem cosmoCoeff_meets_core : CosmoCoeffSpecCore cosmoCoeff where
  defining n a t _ := rfl
  taylor_law := cosmoCoeff_taylor_law
  zero a t h := by simp [cosmoCoeff, h.1.ne']
  one a t h := by
    simp only [cosmoCoeff, cc_hubble_eq, iteratedDeriv_one, pow_one]
    have := h.1.ne'; have := h.2.2
    field_simp
  rescale_invariant n a c t hc h := by
    simp only [cosmoCoeff, cc_hubble_eq, iteratedDeriv_const_mul_field, deriv_const_mul_field']
    have := hc.ne'
    rw [mul_div_mul_left _ _ this]
    field_simp
  time_translate n a τ t h := by
    have e : (fun s => a (s + τ)) = fun s => a (τ + s) := by funext s; rw [add_comm]
    have hk : ∀ k, iteratedDeriv k (fun s => a (s + τ)) t = iteratedDeriv k a (t + τ) := by
      intro k; rw [e, iteratedDeriv_comp_const_add, add_comm]
    have h1 := hk 1
    simp only [iteratedDeriv_one] at h1
    simp only [cosmoCoeff, cc_hubble_eq, hk, h1]
  de_sitter n A h t hA hh := by
    have h1 : deriv (fun s => A * Real.exp (h * s)) t = A * (h * Real.exp (h * t)) := by
      have := iteratedDeriv_dS 1 A h t
      simpa [iteratedDeriv_one] using this
    simp only [cosmoCoeff, cc_hubble_eq, iteratedDeriv_dS, h1]
    have := Real.exp_pos (h * t)
    field_simp
  power_law n p t ht hp := cosmoCoeff_powerLaw n p t ht hp
  milne n t ht hn := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    simp only [cosmoCoeff]
    rw [show m + 2 = m + 2 from rfl, iteratedDeriv_milne, zero_div]
  matter_q t ht := by
    rw [cosmoCoeff_powerLaw 2 _ t ht (by norm_num)]
    norm_num [Finset.prod_range_succ]
  matter_j t ht := by
    rw [cosmoCoeff_powerLaw 3 _ t ht (by norm_num)]
    norm_num [Finset.prod_range_succ]
  not_q_sign := by
    rw [cosmoCoeff_powerLaw 2 _ 1 one_pos (by norm_num)]
    norm_num [Finset.prod_range_succ]
  not_unnormalized := by
    have e : (fun s => Real.exp (2 * s)) = fun s => 1 * Real.exp (2 * s) := by funext s; ring
    have h1 : deriv (fun s => 1 * Real.exp (2 * s)) 0 = 1 * (2 * Real.exp (2 * 0)) := by
      have := iteratedDeriv_dS 1 1 2 0
      simpa [iteratedDeriv_one] using this
    rw [e]
    simp only [cosmoCoeff, cc_hubble_eq, iteratedDeriv_dS, h1]
    norm_num

/-- **Pinning:** every `C` obeying the cosmographic Taylor law equals `cosmoCoeff` wherever
`a > 0`, `a` is `Cⁿ` near `t₀` and `ȧ(t₀) ≠ 0`. -/
theorem cosmoCoeffCore_pins (C : ℕ → (ℝ → ℝ) → ℝ → ℝ) (h : CosmoCoeffSpecCore C) (n : ℕ)
    (a : ℝ → ℝ) (t₀ : ℝ) (hok : CoeffOK n a t₀) : C n a t₀ = cosmoCoeff n a t₀ := by
  set H := deriv a t₀ / a t₀ with hH
  have hH0 : H ≠ 0 := div_ne_zero hok.2.2 hok.1.ne'
  have hdiff := (h.taylor_law n a t₀ hok).sub (cosmoCoeff_taylor_law n a t₀ hok)
  have hp : (fun Δ : ℝ => ∑ k ∈ Finset.range (n + 1),
      ((cosmoCoeff k a t₀ - C k a t₀) * H ^ k / (k.factorial : ℝ)) * Δ ^ k)
      =o[𝓝[≠] 0] fun Δ => Δ ^ n := by
    refine (hdiff.mono nhdsWithin_le_nhds).congr' (Eventually.of_forall fun Δ => ?_)
      EventuallyEq.rfl
    simp only [← hH]
    rw [sub_sub_sub_cancel_left, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : (k.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  have h0 := poly_littleO_coeff_zero n _ hp n le_rfl
  have : (n.factorial : ℝ) ≠ 0 := by positivity
  have hHn : H ^ n ≠ 0 := pow_ne_zero _ hH0
  rw [div_eq_zero_iff, mul_eq_zero] at h0
  rcases h0 with (h0 | h0) | h0
  · linarith
  · exact absurd h0 hHn
  · exact absurd h0 this

end Checked.Fidelity
