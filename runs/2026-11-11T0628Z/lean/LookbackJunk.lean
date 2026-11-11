import Checked.Trust.NonVacuity
import Checked.Cosmography.CCSLookback
import Checked.Cosmography.LookbackThird
import Mathlib.Analysis.Calculus.Deriv.Abs

open Set Filter Topology Asymptotics
open Checked.Cosmography Checked.Cosmography.Aviles

namespace Checked.Trust.NCD

/-! ### Scale factors with one derivative too few: `1 + t + tⁿ|t|` -/

/-- `t^(n+1) |t|` has derivative `(n + 2) xⁿ |x|` at every `x`. -/
theorem pabs_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => t ^ (n + 1) * |t|) ((n + 2) * x ^ n * |x|) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have h := (hasDerivAt_pow (n + 1) x).mul (hasDerivAt_abs_neg hx)
    convert h using 1
    rw [abs_of_neg hx]; simp only [Nat.add_sub_cancel]; push_cast; ring
  · have h1 : HasDerivWithinAt (fun t : ℝ => t ^ (n + 1) * |t|) 0 (Ici 0) 0 := by
      have := (hasDerivAt_pow (n + 2) (0 : ℝ)).hasDerivWithinAt (s := Ici 0)
      refine (this.congr (fun t ht => ?_) (by simp)).congr_deriv (by simp)
      simp only [mem_Ici] at ht
      simp only [abs_of_nonneg ht]; ring
    have h2 : HasDerivWithinAt (fun t : ℝ => t ^ (n + 1) * |t|) 0 (Iic 0) 0 := by
      have := ((hasDerivAt_pow (n + 2) (0 : ℝ)).neg).hasDerivWithinAt (s := Iic 0)
      refine (this.congr (fun t ht => ?_) (by simp)).congr_deriv (by simp)
      simp only [mem_Iic] at ht
      simp only [abs_of_nonpos ht, Pi.neg_apply]; ring
    have := h1.union h2
    rw [Ici_union_Iic, hasDerivWithinAt_univ] at this
    convert this using 1; simp
  · have h := (hasDerivAt_pow (n + 1) x).mul (hasDerivAt_abs_pos hx)
    convert h using 1
    rw [abs_of_pos hx]; simp only [Nat.add_sub_cancel]; push_cast; ring

theorem pabs_deriv (n : ℕ) (c : ℝ) :
    deriv (fun t : ℝ => c * (t ^ (n + 1) * |t|)) = fun x => c * (n + 2) * (x ^ n * |x|) := by
  funext x; rw [((pabs_hasDerivAt n x).const_mul c).deriv]; ring

/-- `1 + t + tⁿ⁺¹|t|`: `C^(n+1)` but not `C^(n+2)` at `0`. -/
noncomputable def kink (n : ℕ) (t : ℝ) : ℝ := 1 + t + t ^ (n + 1) * |t|

theorem kink_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (kink n) (1 + (n + 2) * (x ^ n * |x|)) x := by
  have := ((hasDerivAt_id' x).const_add 1).add (pabs_hasDerivAt n x)
  convert this using 1
  · funext t; simp only [kink, Pi.add_apply]
  · ring

theorem kink_deriv (n : ℕ) : deriv (kink n) = fun x : ℝ => 1 + ((n : ℝ) + 2) * (x ^ n * |x|) := by
  funext x; exact (kink_hasDerivAt n x).deriv

theorem kink_ne (n : ℕ) : kink n 0 ≠ 0 := by simp [kink]

theorem kink_hubble (n : ℕ) : hubble (kink n) 0 = 1 := by
  rw [hubble, kink_deriv]; simp [kink]

/-- The algebra of the lookback remainder in `kink n`: with `z = 1/a − 1` and `a = 1 + t + g`,
`−t − z(1 − z + … ± zⁿ) = g ± a zⁿ⁺¹`. Fifth order: `−t − z(1 − z + z² − z³ + z⁴) = g − a z⁶`. -/
theorem kink_z (n : ℕ) (t : ℝ) (ha : kink n t ≠ 0) :
    redshift (kink n) 0 t = 1 / kink n t - 1 := by
  simp [redshift, kink]

/-- Near `0`, `|z| ≤ 4|t|` and `kink n` stays above `1/2`. -/
theorem kink_bounds (n : ℕ) : ∀ᶠ t in 𝓝 (0 : ℝ), 1 / 2 ≤ kink n t ∧
    |redshift (kink n) 0 t| ≤ 4 * |t| := by
  have hlt : ∀ᶠ t in 𝓝 (0 : ℝ), |t| < 1 / 4 := by
    have : Iio (1 / 4 : ℝ) ∈ 𝓝 |(0 : ℝ)| := Iio_mem_nhds (by norm_num)
    exact (continuous_abs.continuousAt.preimage_mem_nhds this)
  filter_upwards [hlt] with t ht
  have hn : abs (t ^ (n + 1) * |t|) ≤ |t| := by
    rw [abs_mul, abs_abs, abs_pow]
    have h1 : |t| ^ (n + 1) ≤ 1 := pow_le_one₀ (abs_nonneg t) (by linarith)
    nlinarith [abs_nonneg t]
  have hg := abs_le.1 hn
  have ht' := abs_lt.1 ht
  have hk : 1 / 2 ≤ kink n t := by
    unfold kink; nlinarith [abs_nonneg t]
  refine ⟨hk, ?_⟩
  have hpos : 0 < kink n t := by linarith
  rw [kink_z n t hpos.ne']
  have hz : 1 / kink n t - 1 = -(t + t ^ (n + 1) * |t|) / kink n t := by
    field_simp; unfold kink; ring
  rw [hz, abs_div, abs_of_pos hpos, div_le_iff₀ hpos, abs_neg]
  have : abs (t + t ^ (n + 1) * |t|) ≤ 2 * |t| := by
    calc abs (t + t ^ (n + 1) * |t|) ≤ |t| + abs (t ^ (n + 1) * |t|) := abs_add_le _ _
      _ ≤ 2 * |t| := by linarith
  nlinarith [abs_nonneg t]

/-- If `tⁿ⁺¹|t| = o(zⁿ⁺¹)` in `kink n`, contradiction: `|z| ≤ 4|t|`. -/
theorem kink_not_littleO (n : ℕ) :
    ¬ (fun t : ℝ => t ^ (n + 1) * |t|) =o[𝓝 0] (fun t => redshift (kink n) 0 t ^ (n + 2)) := by
  intro h
  have hc : (0 : ℝ) < 1 / (2 * 4 ^ (n + 2)) := by positivity
  have h1 := h.def hc
  have h2 : ∀ᶠ t in 𝓝 (0 : ℝ), t = 0 := by
    filter_upwards [h1, kink_bounds n] with t ht hb
    have hz : |redshift (kink n) 0 t| ^ (n + 2) ≤ (4 * |t|) ^ (n + 2) :=
      pow_le_pow_left₀ (abs_nonneg _) hb.2 _
    simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_abs] at ht
    rw [mul_pow] at hz
    have h4 : (0 : ℝ) < 4 ^ (n + 2) := by positivity
    have key : |t| ^ (n + 1) * |t| ≤ |t| ^ (n + 1) * |t| / 2 := by
      calc |t| ^ (n + 1) * |t| ≤ 1 / (2 * 4 ^ (n + 2)) * |redshift (kink n) 0 t| ^ (n + 2) := ht
        _ ≤ 1 / (2 * 4 ^ (n + 2)) * (4 ^ (n + 2) * |t| ^ (n + 2)) := by gcongr
        _ = |t| ^ (n + 1) * |t| / 2 := by field_simp; ring
    have : |t| ^ (n + 1) * |t| ≤ 0 := by linarith
    have : |t| ^ (n + 2) = 0 := by
      apply le_antisymm _ (by positivity); rw [pow_succ]; exact this
    simpa using this
  have hne : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ≠ 0 := self_mem_nhdsWithin
  have := (h2.filter_mono nhdsWithin_le_nhds).and hne
  exact (this.exists).elim fun t ht => ht.2 ht.1

theorem kink_cont (n : ℕ) : Continuous (kink n) := by unfold kink; fun_prop

theorem kink_z_tendsto (n : ℕ) : Tendsto (fun t => redshift (kink n) 0 t) (𝓝 0) (𝓝 0) := by
  have h4 : Tendsto (fun t : ℝ => 4 * |t|) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_abs.tendsto (0 : ℝ)).const_mul 4
  refine squeeze_zero_norm' ?_ h4
  filter_upwards [kink_bounds n] with t ht
  simpa [Real.norm_eq_abs] using ht.2

/-- `a z^(m+1) = o(z^m)` in `kink n`. -/
theorem kink_az (n m : ℕ) : (fun t => kink n t * redshift (kink n) 0 t ^ (m + 1)) =o[𝓝 0]
    (fun t => redshift (kink n) 0 t ^ m) := by
  have ht : Tendsto (fun t => kink n t * redshift (kink n) 0 t) (𝓝 0) (𝓝 0) := by
    simpa using ((kink_cont n).tendsto 0).mul (kink_z_tendsto n)
  have := (isLittleO_one_iff ℝ).2 ht |>.mul_isBigO (isBigO_refl (fun t => redshift (kink n) 0 t ^ m) (𝓝 0))
  refine this.congr' (Eventually.of_forall fun t => ?_) (Eventually.of_forall fun t => ?_) <;>
    simp only [one_mul] <;> ring

/-- The remainder of the second-order lookback series in `kink 0` (`a = 1 + t + t|t|`):
`−t − z + z² = t|t| + a z³`. -/
theorem kink0_rem : ∀ᶠ t in 𝓝 (0 : ℝ),
    (0 - t) - (redshift (kink 0) 0 t - (1 + 0 / 2) * redshift (kink 0) 0 t ^ 2) / 1 =
      t ^ (0 + 1) * |t| + kink 0 t * redshift (kink 0) 0 t ^ 3 := by
  filter_upwards [kink_bounds 0] with t ht
  have hpos : kink 0 t ≠ 0 := by linarith [ht.1]
  rw [kink_z 0 t hpos]
  field_simp
  unfold kink; ring

theorem kink0_deriv2 : deriv (deriv (kink 0)) 0 = 0 := by
  rw [kink_deriv]
  have : (fun x : ℝ => 1 + ((0 : ℕ) + 2 : ℝ) * (x ^ 0 * |x|)) = fun x => 1 + 2 * |x| := by
    funext x; norm_num
  rw [this]
  apply deriv_zero_of_not_differentiableAt
  intro h
  apply not_differentiableAt_abs_zero
  have := (h.const_add (-1)).const_mul (1 / 2 : ℝ)
  convert this using 1; funext x; ring

/-- Differentiability of `ȧ` at `t₀` is needed in `lookback_second_order`: `a = 1 + t + t|t|` is
differentiable with `ȧ(0) = 1`, but `ȧ = 1 + 2|t|` has no derivative at `0`; Lean's junk value
`ä(0) = 0` gives `q₀ = 0`, and the remainder is `t|t| + a z³`, not `o(z²)`. -/
theorem lookback_second_order_h2 : necessity% Checked.Cosmography.lookback_second_order 2 := by
  refine ⟨kink 0, 0, Eventually.of_forall fun t => (kink_hasDerivAt 0 t).differentiableAt,
    kink_ne 0, by rw [kink_deriv]; norm_num, ?_⟩
  intro h
  have hH : hubble (kink 0) 0 = 1 := kink_hubble 0
  have hq : decel (kink 0) 0 = 0 := by simp [decel, kink0_deriv2]
  rw [hH, hq] at h
  have hg := (h.congr' kink0_rem EventuallyEq.rfl).sub (kink_az 0 2)
  apply kink_not_littleO 0
  refine hg.congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
  ring

/-- Eventual differentiability of `a` is redundant in `lookback_second_order`: `ȧ` differentiable at
`t₀` with `ȧ(t₀) ≠ 0` is continuous there, so `ȧ ≠ 0` near `t₀`, and a nonzero `deriv` value means
`a` is differentiable (Lean's junk derivative is `0`). -/
theorem lookback_second_order_r1 : dropped% Checked.Cosmography.lookback_second_order 1 := by
  intro a t₀ ha' ha0 hH
  exact lookback_second_order a t₀ ((ha'.continuousAt.eventually_ne hH).mono
    fun t ht => differentiableAt_of_deriv_ne_zero ht) ha' ha0 hH

/-! ### Fifth order: `kink 3` (`a = 1 + t + t⁴|t|`, `C⁴` but not `C⁵`) -/

theorem kink3_d1 : deriv (kink 3) = fun x : ℝ => 1 + 5 * (x ^ 3 * |x|) := by
  rw [kink_deriv]; funext x; norm_num

theorem kink3_d2 : deriv (fun x : ℝ => 1 + 5 * (x ^ 3 * |x|)) = fun x => 20 * (x ^ 2 * |x|) := by
  funext x; apply HasDerivAt.deriv
  have := ((pabs_hasDerivAt 2 x).const_mul 5).const_add 1
  convert this using 1; push_cast; ring

theorem kink3_d3 : deriv (fun x : ℝ => 20 * (x ^ 2 * |x|)) = fun x => 60 * (x * |x|) := by
  funext x; apply HasDerivAt.deriv
  have := (pabs_hasDerivAt 1 x).const_mul 20
  convert this using 1; push_cast; ring

theorem kink3_d4 : deriv (fun x : ℝ => 60 * (x * |x|)) = fun x => 120 * |x| := by
  funext x; apply HasDerivAt.deriv
  have := (pabs_hasDerivAt 0 x).const_mul 60
  convert this using 1
  · funext t; ring
  · push_cast; ring

theorem kink3_d5 : deriv (fun x : ℝ => 120 * |x|) 0 = 0 := by
  rw [deriv_const_mul_field']; simp [deriv_abs_zero]

theorem kink3_coeffs : decel (kink 3) 0 = 0 ∧ cosmoCoeff 3 (kink 3) 0 = 0 ∧
    cosmoCoeff 4 (kink 3) 0 = 0 ∧ cosmoCoeff 5 (kink 3) 0 = 0 := by
  have i3 : iteratedDeriv 3 (kink 3) 0 = 0 := by
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, kink3_d1, kink3_d2, kink3_d3]; simp
  have i4 : iteratedDeriv 4 (kink 3) 0 = 0 := by
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, kink3_d1,
      kink3_d2, kink3_d3, kink3_d4]; simp
  have i5 : iteratedDeriv 5 (kink 3) 0 = 0 := by
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ,
      iteratedDeriv_one, kink3_d1, kink3_d2, kink3_d3, kink3_d4, kink3_d5]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [decel, kink3_d1, kink3_d2]; simp
  all_goals simp [cosmoCoeff, i3, i4, i5]

/-- Fifth-order lookback remainder in `kink 3`: `−t − z(1 − z + z² − z³ + z⁴) = t⁴|t| − a z⁶`. -/
theorem kink3_rem : ∀ᶠ t in 𝓝 (0 : ℝ), CCS.remainder CCS.correctD4 (kink 3) 0 t =
    t ^ (3 + 1) * |t| - kink 3 t * redshift (kink 3) 0 t ^ (5 + 1) := by
  filter_upwards [kink_bounds 3] with t ht
  have hpos : kink 3 t ≠ 0 := by linarith [ht.1]
  obtain ⟨hq, hj, hs, hl⟩ := kink3_coeffs
  have hz1 : kink 3 t * (1 + redshift (kink 3) 0 t) = 1 := by
    rw [kink_z 3 t hpos]; field_simp; ring
  simp only [CCS.remainder, CCS.series, CCS.correctD4, CCS.D1, CCS.D2, CCS.D3, hq, hj, hs, hl,
    kink_hubble]
  set z := redshift (kink 3) 0 t
  have hk : kink 3 t = 1 + t + t ^ 4 * |t| := rfl
  rw [hk] at hz1 ⊢
  linear_combination (z ^ 5 - z ^ 4 + z ^ 3 - z ^ 2 + z - 1) * hz1

/-- Smoothness (`C⁵` at `t₀`) is needed in `CCS.lookback_fifth_order`: `a = 1 + t + t⁴|t|` is `C⁴`
with `ȧ(0) = 1`; its fourth derivative `120|t|` has no derivative at `0`, Lean's junk value gives
`l₀ = 0`, and the remainder is `t⁴|t| − a z⁶`, not `o(z⁵)`. -/
theorem lookback_fifth_order_h1 : necessity% Checked.Cosmography.CCS.lookback_fifth_order 1 := by
  refine ⟨kink 3, 0, kink_ne 3, by rw [kink_hubble]; norm_num, fun h => ?_⟩
  have hg := (h.congr' kink3_rem EventuallyEq.rfl).add (kink_az 3 5)
  apply kink_not_littleO 3
  refine hg.congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
  ring

end Checked.Trust.NCD
