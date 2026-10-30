import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Checked.Cosmography.BambaZ

/-!
# `yred`, `omega0`, `curvK` pinned by blind textbook specifications (trust track T1)

After `redshift` and `cosmoCoeff` (`RedshiftCoeffSpecs.lean`), the most-used unpinned physics
definitions in `TRUST_MAP.md` were `BambaY.yred` (30 headlines), `BambaK.omega0` (21) and
`BambaZ.curvK` (15). The structures below are copied **verbatim** (all fields) from
`Work/Fidelity/BlindSpecs3.lean` (frozen in commit f15af15), written by a subagent that did not
read any repository definition. We prove that the program's definitions meet them and that each
specification pins its definition through its determining law.
-/

namespace Checked.Fidelity

open Filter Topology Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.BambaK
open Checked.Cosmography.BambaZ

/-- Specification of the y-redshift `Y a t₀ t = z / (1 + z) = 1 − a(t)/a(t₀)` [CV07, §II].
It maps `z ∈ (−1, ∞)` bijectively onto `y ∈ (−∞, 1)`. Every field is only demanded on the
physical domain `a t₀ > 0`, `a t > 0`. -/
structure YRedSpec (Y : (ℝ → ℝ) → ℝ → ℝ → ℝ) : Prop where
  /-- Determining law [CV07, §II: `y = z/(1+z) = 1 − a(t)/a(t₀)`]. -/
  law : ∀ (a : ℝ → ℝ) (t₀ t : ℝ), 0 < a t₀ → 0 < a t → Y a t₀ t = 1 - a t / a t₀
  /-- Definition through the ordinary redshift `z = a(t₀)/a(t) − 1` [CV07, §II]. -/
  of_z : ∀ (a : ℝ → ℝ) (t₀ t : ℝ), 0 < a t₀ → 0 < a t →
    Y a t₀ t = (a t₀ / a t - 1) / (1 + (a t₀ / a t - 1))
  /-- Inverse map `z = y / (1 − y)` [CV07, §II]. -/
  inv_z : ∀ (a : ℝ → ℝ) (t₀ t : ℝ), 0 < a t₀ → 0 < a t →
    a t₀ / a t - 1 = Y a t₀ t / (1 - Y a t₀ t)
  /-- Range: `y < 1` for every physical (positive) scale factor [CV07, §II]. -/
  lt_one : ∀ (a : ℝ → ℝ) (t₀ t : ℝ), 0 < a t₀ → 0 < a t → Y a t₀ t < 1
  /-- Sign: `y > 0` exactly for redshift (`a t < a t₀`), `y < 0` for blueshift. -/
  pos_iff : ∀ (a : ℝ → ℝ) (t₀ t : ℝ), 0 < a t₀ → 0 < a t → (0 < Y a t₀ t ↔ a t < a t₀)
  /-- Order preservation: `y` is strictly increasing in `z`, i.e. decreasing in `a t`. -/
  strictAnti_a : ∀ (a b : ℝ → ℝ) (t₀ t : ℝ), 0 < a t₀ → 0 < a t → 0 < b t →
    b t₀ = a t₀ → a t < b t → Y b t₀ t < Y a t₀ t
  /-- No redshift at the observation time. -/
  self : ∀ (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → Y a t₀ t₀ = 0
  /-- Anchor: de Sitter `a = exp(H t)` gives `y = 1 − exp(H (t − t₀))` [Ryd16, §5.3]. -/
  deSitter : ∀ (H t₀ t : ℝ), Y (fun s => Real.exp (H * s)) t₀ t = 1 - Real.exp (H * (t - t₀))
  /-- Anchor: Milne universe `a = t` gives `y = 1 − t/t₀` (for `t, t₀ > 0`) [Ryd16, §5.2]. -/
  milne : ∀ (t₀ t : ℝ), 0 < t₀ → 0 < t → Y (fun s => s) t₀ t = 1 - t / t₀
  /-- Anchor value: Milne, `t₀ = 2`, `t = 1`, so `z = 1` and `y = 1/2`. -/
  milne_value : Y (fun s => s) 2 1 = 1 / 2
  /-- Anchor: static universe `a ≡ c > 0` has no redshift. -/
  static : ∀ (c t₀ t : ℝ), 0 < c → Y (fun _ => c) t₀ t = 0
  /-- Invariance: `y` depends only on ratios of the scale factor, so it is unchanged by
  rescaling `a ↦ c · a` (`c > 0`), equivalently by the normalisation of `a`. -/
  scale_inv : ∀ (c : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ), 0 < c → 0 < a t₀ → 0 < a t →
    Y (fun s => c * a s) t₀ t = Y a t₀ t
  /-- Invariance under time translation of the cosmic clock. -/
  shift_inv : ∀ (τ : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ), 0 < a t₀ → 0 < a t →
    Y (fun s => a (s + τ)) (t₀ - τ) (t - τ) = Y a t₀ t
  /-- Locality: `y` depends only on the two values `a t₀`, `a t`. -/
  local_values : ∀ (a b : ℝ → ℝ) (t₀ t : ℝ), 0 < a t₀ → 0 < a t →
    a t₀ = b t₀ → a t = b t → Y a t₀ t = Y b t₀ t
  /-- Near miss: `y ≠ z / (1 − z)` (Milne, `t₀ = 3`, `t = 1`: `z = 2`, `z/(1−z) = −2`,
  but `y = 2/3`). -/
  not_z_div_one_sub_z : Y (fun s => s) 3 1 ≠ -2
  /-- Near miss: `y ≠ z` (Milne, `t₀ = 2`, `t = 1`: `z = 1`, `y = 1/2`). -/
  not_z : Y (fun s => s) 2 1 ≠ 1
  /-- Near miss (sign flip): `y ≠ a(t)/a(t₀) − 1` (that would give `−1/2` here). -/
  not_neg : Y (fun s => s) 2 1 ≠ -1 / 2
  /-- Near miss: `y ≠ 1 − a(t₀)/a(t) = −z` (that would give `−1` here). -/
  not_neg_z : Y (fun s => s) 2 1 ≠ -1
  /-- Near miss: `y ≠ log(1 + z)` (that would give `log 2` here). -/
  not_log : Y (fun s => s) 2 1 ≠ Real.log 2

/-- Specification of `O K a t₀ = Ω₀ = ρ_total(t₀) / ρ_crit(t₀)` for an FLRW model with curvature
constant `K`. From the Friedmann equation `H² = (8πG/3)ρ − K/a²` and `ρ_crit = 3H²/(8πG)`:
`Ω₀ = 1 + K / (a₀ H₀)² = 1 + K / ȧ(t₀)²` [Wei08, eq. (1.5.19)–(1.5.21); Ryd16, eq. (4.34)].
All fields demand values only when `a t₀ > 0`, `a` is differentiable at `t₀`, and `H₀ ≠ 0`. -/
structure Omega0Spec (O : ℝ → (ℝ → ℝ) → ℝ → ℝ) : Prop where
  /-- Determining law: `Ω₀ = 1 + K/(a₀ H₀)²` [Ryd16, eq. (4.34): `1 − Ω₀ = −K/(a₀H₀)²`]. -/
  law : ∀ (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → DifferentiableAt ℝ a t₀ →
    deriv a t₀ / a t₀ ≠ 0 →
    O K a t₀ = 1 + K / (a t₀ ^ 2 * (deriv a t₀ / a t₀) ^ 2)
  /-- Defining law via the Friedmann equation: if the total density `ρ` satisfies
  `H₀² = (8πG/3)ρ − K/a₀²` (for some `G > 0`), then `Ω₀ = ρ / ρ_crit = (8πG/3)ρ / H₀²`
  [Wei08, §1.5; Dod03, §2.4]. -/
  friedmann : ∀ (G ρ K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < G → 0 < a t₀ →
    DifferentiableAt ℝ a t₀ → deriv a t₀ / a t₀ ≠ 0 →
    (deriv a t₀ / a t₀) ^ 2 = 8 * Real.pi * G / 3 * ρ - K / a t₀ ^ 2 →
    O K a t₀ = ρ / (3 * (deriv a t₀ / a t₀) ^ 2 / (8 * Real.pi * G))
  /-- Anchor: spatially flat (`K = 0`) ⇒ `Ω₀ = 1` [Ryd16, §4.4]. -/
  flat : ∀ (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → DifferentiableAt ℝ a t₀ →
    deriv a t₀ / a t₀ ≠ 0 → O 0 a t₀ = 1
  /-- Anchor: Milne (empty) universe `a = t`, `K = −1` ⇒ `Ω₀ = 0` [Ryd16, §5.2]. -/
  milne : ∀ t₀ : ℝ, 0 < t₀ → O (-1) (fun s => s) t₀ = 0
  /-- Anchor: closed de Sitter slicing `a = cosh t`, `K = 1` (`H² = 1 − 1/a²`, i.e. a pure
  cosmological constant with `(8πG/3)ρ_Λ = 1`) ⇒ `Ω₀ = 1/H₀² = 1 + 1/sinh² t₀`. -/
  closed_deSitter : ∀ t₀ : ℝ, t₀ ≠ 0 →
    O 1 Real.cosh t₀ = 1 + 1 / Real.sinh t₀ ^ 2
  /-- Anchor: closed model with `a = t`, `K = 1` (so `ȧ = 1`) ⇒ `Ω₀ = 2`. -/
  closed_value : O 1 (fun s => s) 1 = 2
  /-- Closed (`K > 0`) ⇔ `Ω₀ > 1` [Ryd16, §4.4]. -/
  gt_one_iff : ∀ (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → DifferentiableAt ℝ a t₀ →
    deriv a t₀ / a t₀ ≠ 0 → (1 < O K a t₀ ↔ 0 < K)
  /-- Open (`K < 0`) ⇔ `Ω₀ < 1` [Ryd16, §4.4]. -/
  lt_one_iff : ∀ (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → DifferentiableAt ℝ a t₀ →
    deriv a t₀ / a t₀ ≠ 0 → (O K a t₀ < 1 ↔ K < 0)
  /-- Rescaling law: `(K, a) ↦ (c² K, c · a)` describes the same spacetime, so `Ω₀` is
  unchanged (`c > 0`). -/
  rescale : ∀ (c K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < c → 0 < a t₀ → DifferentiableAt ℝ a t₀ →
    deriv a t₀ / a t₀ ≠ 0 → O (c ^ 2 * K) (fun s => c * a s) t₀ = O K a t₀
  /-- Invariance under time translation. -/
  shift_inv : ∀ (τ K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → DifferentiableAt ℝ a t₀ →
    deriv a t₀ / a t₀ ≠ 0 → O K (fun s => a (s + τ)) (t₀ - τ) = O K a t₀
  /-- Locality: depends only on the germ of `a` at `t₀`. -/
  local_germ : ∀ (K : ℝ) (a b : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → DifferentiableAt ℝ a t₀ →
    deriv a t₀ / a t₀ ≠ 0 → a =ᶠ[𝓝 t₀] b → O K a t₀ = O K b t₀
  /-- Near miss (sign): `Ω₀ ≠ 1 − K/(a₀H₀)²` (closed `a = t`, `K = 1`, `t₀ = 1` would give 0). -/
  not_sign_flip : O 1 (fun s => s) 1 ≠ 0
  /-- Near miss: `Ω₀ ≠ 1 + K/H₀²` (missing `a₀²`): `a = 2t`, `K = 1`, `t₀ = 1` has
  `H₀ = 1`, `a₀ = 2`, so `Ω₀ = 5/4`, not `2`. -/
  not_missing_a0 : O 1 (fun s => 2 * s) 1 ≠ 2

/-- Specification of `k K a t₀ = K / (H₀ a₀)²` (with `c = 1`), the dimensionless curvature
parameter, so that the curvature density parameter is `Ω_k = −k` and `Ω₀ = 1 − Ω_k = 1 + k`
[Wei08, eq. (1.5.21) `Ω_K = −K/(a₀H₀)²`; Dod03, §2.4]. -/
structure CurvKSpec (k : ℝ → (ℝ → ℝ) → ℝ → ℝ) : Prop where
  /-- Determining law `k = K / (H₀ a₀)²`. -/
  law : ∀ (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → DifferentiableAt ℝ a t₀ →
    deriv a t₀ / a t₀ ≠ 0 →
    k K a t₀ = K / ((deriv a t₀ / a t₀) * a t₀) ^ 2
  /-- Equivalent form: `k = K / ȧ(t₀)²`. -/
  law_adot : ∀ (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → DifferentiableAt ℝ a t₀ →
    deriv a t₀ ≠ 0 → k K a t₀ = K / deriv a t₀ ^ 2
  /-- Closure relation `Ω₀ = 1 − Ω_k = 1 + k`: if the total density obeys the Friedmann
  equation `H₀² = (8πG/3)ρ − K/a₀²`, then `(8πG/3)ρ/H₀² = 1 + k` [Wei08, eq. (1.5.20)]. -/
  friedmann : ∀ (G ρ K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < G → 0 < a t₀ →
    DifferentiableAt ℝ a t₀ → deriv a t₀ / a t₀ ≠ 0 →
    (deriv a t₀ / a t₀) ^ 2 = 8 * Real.pi * G / 3 * ρ - K / a t₀ ^ 2 →
    8 * Real.pi * G / 3 * ρ / (deriv a t₀ / a t₀) ^ 2 = 1 + k K a t₀
  /-- Anchor: flat ⇒ `k = 0`. -/
  flat : ∀ (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → DifferentiableAt ℝ a t₀ →
    deriv a t₀ / a t₀ ≠ 0 → k 0 a t₀ = 0
  /-- Anchor: Milne `a = t`, `K = −1` ⇒ `k = −1` (`Ω_k = 1`). -/
  milne : ∀ t₀ : ℝ, 0 < t₀ → k (-1) (fun s => s) t₀ = -1
  /-- Anchor: closed de Sitter `a = cosh t`, `K = 1` ⇒ `k = 1 / sinh² t₀`. -/
  closed_deSitter : ∀ t₀ : ℝ, t₀ ≠ 0 → k 1 Real.cosh t₀ = 1 / Real.sinh t₀ ^ 2
  /-- Sign: `k` has the sign of `K` (closed `k > 0`, open `k < 0`). -/
  pos_iff : ∀ (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → DifferentiableAt ℝ a t₀ →
    deriv a t₀ / a t₀ ≠ 0 → (0 < k K a t₀ ↔ 0 < K)
  neg_iff : ∀ (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → DifferentiableAt ℝ a t₀ →
    deriv a t₀ / a t₀ ≠ 0 → (k K a t₀ < 0 ↔ K < 0)
  /-- Linearity in `K` at fixed expansion history. -/
  linear_K : ∀ (r K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → DifferentiableAt ℝ a t₀ →
    deriv a t₀ / a t₀ ≠ 0 → k (r * K) a t₀ = r * k K a t₀
  /-- Rescaling invariance: `(K, a) ↦ (c² K, c · a)` leaves `k` unchanged (`c > 0`). -/
  rescale : ∀ (c K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < c → 0 < a t₀ → DifferentiableAt ℝ a t₀ →
    deriv a t₀ / a t₀ ≠ 0 → k (c ^ 2 * K) (fun s => c * a s) t₀ = k K a t₀
  /-- Invariance under time translation. -/
  shift_inv : ∀ (τ K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → DifferentiableAt ℝ a t₀ →
    deriv a t₀ / a t₀ ≠ 0 → k K (fun s => a (s + τ)) (t₀ - τ) = k K a t₀
  /-- Near miss (sign): `k ≠ Ω_k = −K/(H₀a₀)²` (Milne would give `+1`). -/
  not_omega_k : k (-1) (fun s => s) 1 ≠ 1
  /-- Near miss: `k ≠ K/H₀²` (missing `a₀`): `a = 2t`, `K = −4`, `t₀ = 1` has `k = −1`,
  while `K/H₀² = −4`. -/
  not_missing_a0 : k (-4) (fun s => 2 * s) 1 ≠ -4
  /-- Anchor value for the preceding near miss. -/
  value_2t : k (-4) (fun s => 2 * s) 1 = -1

/-! ## Proofs: y-redshift -/

lemma yred_eq {a : ℝ → ℝ} {t₀ t : ℝ} (h0 : 0 < a t₀) (h1 : 0 < a t) :
    yred a t₀ t = 1 - a t / a t₀ := by
  have := h0.ne'; have := h1.ne'
  simp only [yred, redshift, add_sub_cancel]
  rw [div_eq_iff (by positivity)]
  field_simp

lemma yred_milne (t₀ t : ℝ) (h₀ : 0 < t₀) (h : 0 < t) : yred (fun s => s) t₀ t = 1 - t / t₀ :=
  yred_eq (a := fun s => s) h₀ h

theorem yred_meets_spec : YRedSpec yred where
  law a t₀ t h0 h1 := yred_eq h0 h1
  of_z a t₀ t _ _ := rfl
  inv_z a t₀ t h0 h1 := by
    rw [yred_eq h0 h1]
    have := h0.ne'; have := h1.ne'
    rw [sub_sub_cancel, eq_div_iff (by positivity)]
    field_simp
  lt_one a t₀ t h0 h1 := by
    rw [yred_eq h0 h1]; have := div_pos h1 h0; linarith
  pos_iff a t₀ t h0 h1 := by
    rw [yred_eq h0 h1, sub_pos, div_lt_one h0]
  strictAnti_a a b t₀ t h0 h1 hb hab hlt := by
    have hb0 : 0 < b t₀ := hab ▸ h0
    rw [yred_eq h0 h1, yred_eq hb0 hb, hab]
    have := div_lt_div_of_pos_right hlt h0
    linarith
  self a t₀ h := by simp [yred, redshift, h.ne']
  deSitter H t₀ t := by
    rw [yred_eq (a := fun s => Real.exp (H * s)) (Real.exp_pos _) (Real.exp_pos _), ← Real.exp_sub]
    ring_nf
  milne t₀ t h₀ h := yred_milne t₀ t h₀ h
  milne_value := by rw [yred_milne 2 1 (by norm_num) (by norm_num)]; norm_num
  static c t₀ t hc := by rw [yred_eq (a := fun _ => c) hc hc]; simp [hc.ne']
  scale_inv c a t₀ t hc h0 h1 := by
    rw [yred_eq (a := fun s => c * a s) (mul_pos hc h0) (mul_pos hc h1), yred_eq h0 h1,
      mul_div_mul_left _ _ hc.ne']
  shift_inv τ a t₀ t _ _ := by simp only [yred, redshift, sub_add_cancel]
  local_values a b t₀ t _ _ h1 h2 := by simp only [yred, redshift, h1, h2]
  not_z_div_one_sub_z := by rw [yred_milne 3 1 (by norm_num) (by norm_num)]; norm_num
  not_z := by rw [yred_milne 2 1 (by norm_num) (by norm_num)]; norm_num
  not_neg := by rw [yred_milne 2 1 (by norm_num) (by norm_num)]; norm_num
  not_neg_z := by rw [yred_milne 2 1 (by norm_num) (by norm_num)]; norm_num
  not_log := by
    rw [yred_milne 2 1 (by norm_num) (by norm_num)]
    intro h
    have h1 := Real.add_one_lt_exp (show (-1 / 2 : ℝ) ≠ 0 by norm_num)
    have h2 : Real.exp (1 / 2) * Real.exp (-1 / 2) = 1 := by rw [← Real.exp_add]; norm_num
    have h3 : Real.exp (1 / 2) < 2 := by nlinarith [Real.exp_pos (1 / 2 : ℝ)]
    have h4 : (1 : ℝ) / 2 < Real.log 2 := (Real.lt_log_iff_exp_lt (by norm_num)).2 h3
    linarith

/-- **Pinning:** any `Y` meeting `YRedSpec` is `yred` wherever `a t₀, a t > 0`. -/
theorem yRedSpec_pins (Y : (ℝ → ℝ) → ℝ → ℝ → ℝ) (h : YRedSpec Y) (a : ℝ → ℝ) (t₀ t : ℝ)
    (h0 : 0 < a t₀) (h1 : 0 < a t) : Y a t₀ t = yred a t₀ t := by
  rw [h.law a t₀ t h0 h1, yred_eq h0 h1]

/-! ## Proofs: Ω₀ and k -/

lemma hubble_sq_pos {a : ℝ → ℝ} {t₀ : ℝ} (hH : deriv a t₀ / a t₀ ≠ 0) :
    0 < (deriv a t₀ / a t₀) ^ 2 :=
  lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hH))

lemma omega0_eq (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) :
    omega0 K a t₀ = 1 + K / (a t₀ ^ 2 * (deriv a t₀ / a t₀) ^ 2) := by
  simp only [omega0, hubble]; ring

lemma curvK_eq (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) :
    curvK K a t₀ = K / ((deriv a t₀ / a t₀) * a t₀) ^ 2 := by
  simp only [curvK, hubble]; ring

lemma hubble_id' (t : ℝ) : deriv (fun s : ℝ => s) t / t = 1 / t := by simp

lemma deriv_two_mul (t : ℝ) : deriv (fun s : ℝ => 2 * s) t = 2 := by
  rw [deriv_const_mul_field']; simp

/-- From the Friedmann equation at `t₀`: `K = a₀² (cρ − H₀²)`. -/
lemma K_of_friedmann {K c ρ H a₀ : ℝ} (ha : 0 < a₀) (hF : H ^ 2 = c * ρ - K / a₀ ^ 2) :
    K = a₀ ^ 2 * (c * ρ - H ^ 2) := by
  have : K / a₀ ^ 2 = c * ρ - H ^ 2 := by linarith
  rw [div_eq_iff (by positivity)] at this
  linarith

theorem omega0_meets_spec : Omega0Spec omega0 where
  law K a t₀ _ _ _ := omega0_eq K a t₀
  friedmann G ρ K a t₀ hG ha _ hH hF := by
    rw [omega0_eq, K_of_friedmann ha hF]
    have := hubble_sq_pos hH
    have := Real.pi_pos
    have := ha.ne'
    have hH' : deriv a t₀ ≠ 0 := fun h0 => hH (by rw [h0, zero_div])
    field_simp
    ring
  flat a t₀ _ _ _ := by simp [omega0]
  milne t₀ h := by
    rw [omega0_eq]; simp only [hubble_id']; field_simp; ring
  closed_deSitter t₀ h := by
    have hs : Real.sinh t₀ ≠ 0 := by rwa [ne_eq, Real.sinh_eq_zero]
    have hc := (Real.cosh_pos t₀).ne'
    rw [omega0_eq, Real.deriv_cosh]
    field_simp
  closed_value := by rw [omega0_eq]; simp only [hubble_id']; norm_num
  gt_one_iff K a t₀ ha _ hH := by
    have hD : 0 < a t₀ ^ 2 * (deriv a t₀ / a t₀) ^ 2 := mul_pos (by positivity) (hubble_sq_pos hH)
    rw [omega0_eq, lt_add_iff_pos_right, div_pos_iff_of_pos_right hD]
  lt_one_iff K a t₀ ha _ hH := by
    have hD : 0 < a t₀ ^ 2 * (deriv a t₀ / a t₀) ^ 2 := mul_pos (by positivity) (hubble_sq_pos hH)
    rw [omega0_eq, add_lt_iff_neg_left]
    constructor
    · intro h; by_contra hK; push Not at hK; have := div_nonneg hK hD.le; linarith
    · intro h; exact div_neg_of_neg_of_pos h hD
  rescale c K a t₀ hc ha _ hH := by
    rw [omega0_eq, omega0_eq, deriv_const_mul_field']
    have := hc.ne'; have := ha.ne'
    field_simp
  shift_inv τ K a t₀ _ _ _ := by
    rw [omega0_eq, omega0_eq, deriv_comp_add_const, sub_add_cancel]
  local_germ K a b t₀ _ _ _ h := by
    rw [omega0_eq, omega0_eq, h.deriv_eq, h.eq_of_nhds]
  not_sign_flip := by rw [omega0_eq]; simp only [hubble_id']; norm_num
  not_missing_a0 := by rw [omega0_eq, deriv_two_mul]; norm_num

/-- **Pinning:** any `O` meeting `Omega0Spec` is `omega0` wherever `a₀ > 0`, `a` is
differentiable at `t₀` and `H₀ ≠ 0`. -/
theorem omega0Spec_pins (O : ℝ → (ℝ → ℝ) → ℝ → ℝ) (h : Omega0Spec O) (K : ℝ) (a : ℝ → ℝ)
    (t₀ : ℝ) (ha : 0 < a t₀) (hd : DifferentiableAt ℝ a t₀) (hH : deriv a t₀ / a t₀ ≠ 0) :
    O K a t₀ = omega0 K a t₀ := by
  rw [h.law K a t₀ ha hd hH, omega0_eq]

theorem curvK_meets_spec : CurvKSpec curvK where
  law K a t₀ _ _ _ := curvK_eq K a t₀
  law_adot K a t₀ ha _ hd := by
    rw [curvK_eq]; have := ha.ne'; field_simp
  friedmann G ρ K a t₀ hG ha _ hH hF := by
    rw [curvK_eq, K_of_friedmann ha hF]
    have := hubble_sq_pos hH
    have := ha.ne'
    have hH' : deriv a t₀ ≠ 0 := fun h0 => hH (by rw [h0, zero_div])
    field_simp
    ring
  flat a t₀ _ _ _ := by simp [curvK]
  milne t₀ h := by rw [curvK_eq]; simp only [hubble_id']; field_simp
  closed_deSitter t₀ h := by
    have hs : Real.sinh t₀ ≠ 0 := by rwa [ne_eq, Real.sinh_eq_zero]
    have hc := (Real.cosh_pos t₀).ne'
    rw [curvK_eq, Real.deriv_cosh]
    field_simp
  pos_iff K a t₀ ha _ hH := by
    have hD : 0 < ((deriv a t₀ / a t₀) * a t₀) ^ 2 := by
      rw [mul_pow]; exact mul_pos (hubble_sq_pos hH) (by positivity)
    rw [curvK_eq, div_pos_iff_of_pos_right hD]
  neg_iff K a t₀ ha _ hH := by
    have hD : 0 < ((deriv a t₀ / a t₀) * a t₀) ^ 2 := by
      rw [mul_pow]; exact mul_pos (hubble_sq_pos hH) (by positivity)
    rw [curvK_eq]
    constructor
    · intro h; by_contra hK; push Not at hK; have := div_nonneg hK hD.le; linarith
    · intro h; exact div_neg_of_neg_of_pos h hD
  linear_K r K a t₀ _ _ _ := by rw [curvK_eq, curvK_eq, mul_div_assoc]
  rescale c K a t₀ hc ha _ hH := by
    rw [curvK_eq, curvK_eq, deriv_const_mul_field']
    have := hc.ne'; have := ha.ne'
    field_simp
  shift_inv τ K a t₀ _ _ _ := by
    rw [curvK_eq, curvK_eq, deriv_comp_add_const, sub_add_cancel]
  not_omega_k := by rw [curvK_eq]; simp only [hubble_id']; norm_num
  not_missing_a0 := by rw [curvK_eq, deriv_two_mul]; norm_num
  value_2t := by rw [curvK_eq, deriv_two_mul]; norm_num

/-- **Pinning:** any `k` meeting `CurvKSpec` is `curvK` wherever `a₀ > 0`, `a` is
differentiable at `t₀` and `H₀ ≠ 0`. -/
theorem curvKSpec_pins (k : ℝ → (ℝ → ℝ) → ℝ → ℝ) (h : CurvKSpec k) (K : ℝ) (a : ℝ → ℝ)
    (t₀ : ℝ) (ha : 0 < a t₀) (hd : DifferentiableAt ℝ a t₀) (hH : deriv a t₀ / a t₀ ≠ 0) :
    k K a t₀ = curvK K a t₀ := by
  rw [h.law K a t₀ ha hd hH, curvK_eq]

end Checked.Fidelity
