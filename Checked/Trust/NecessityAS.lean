import Checked.Cosmography.B1L19CurvedTools
import Checked.Trust.NecessityAR
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Hypothesis necessity, B1 family: models of every expansion history in the ΛCDM family (trust track T2b)

Run 2026-11-18T1228Z. Earlier necessity witnesses for the B1 headlines used only the closed-form
universes (de Sitter, Einstein–de Sitter, the flat model of negative cosmological constant), so every
hypothesis whose witness needs another matter density or a curved universe stayed open.

* **A scale factor for every member of the family** (`ma`): for matter density `m`, curvature term `k`
  and any lower end `c` in `(0, 1]` with `y(v) = m + k v² + (1 − m − k) v⁶` positive on `[c, 1]`, cosmic
  time as the integral of `v² · 2/√y` in `v = √(a/a₀)` (clamped outside `[c, 1]` so that it is a strictly
  increasing bijection of the line) has an inverse `V`, and `a = V²` obeys the law
  `H = H₀ √(m(1+z)³ + k(1+z)² + 1 − k − m)` with `H₀ = a₀ = 1` wherever `V ∈ [c, 1]` (`ma_law`); its
  comoving distance to the source at `v = w` is `∫_w^1 2/√y` (`ma_comoving`). No closed form is needed.
* **The upper bound on the total density of the curved Lusso et al. 2019 pair is NEEDED**
  (`l19_sq_curved_h9`, `l19_sqg_curved_h9`): the closed model of matter density one half and total density
  two (curvature constant one); crude one- and two-step bounds put the comoving distance to the middle
  source within a few tenths of a right angle, so the transverse distance there is near its maximum and
  the residual at the farther source does not exceed the one at the middle source.
* **The redshift of the farthest source in `rl19_box_unmatched` is NEEDED** (`rl19_box_unmatched_h12`): the
  flat model of matter density eleven twentieths with the farthest source placed at the middle one; a cubic
  inside the box matches the remaining moduli (eight-step lower and upper sums of the distance integrals).
* **The expansion law of `cubic_separation` and `cubic_direction` is NEEDED** (`cubic_separation_h8`,
  `cubic_direction_h8`): the Einstein–de Sitter universe, read with the density parameter one fifth; its
  exact distances at redshifts three and seven are matched by a cubic near the ΛCDM-implied point
  (separation) and by one on the other side of the line (direction). Residuals are bounded through
  hundredth powers of interval ends (`resid_band100`).
* **The upper density bound `Ω ≤ 1` of `fit_direction` is NEEDED** (`fit_direction_h2`): the flat model of
  negative cosmological constant at three halves; a cubic matches all three moduli and lies on the other
  side of the line (eight-step sums refined toward the steep end).
-/

namespace Checked.Trust.NCAS

open Set Filter Topology MeasureTheory Real
open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.BambaK
open Checked.Cosmography.B1L19CurvedTools

/-- The clamp of `x` to `[c, 1]`. -/
noncomputable def mclamp (c x : ℝ) : ℝ := max c (min x 1)

theorem mclamp_mem {c : ℝ} (hc1 : c ≤ 1) (x : ℝ) : mclamp c x ∈ Icc c 1 :=
  ⟨le_max_left _ _, max_le hc1 (min_le_right _ _)⟩

theorem mclamp_eq {c x : ℝ} (hx : x ∈ Icc c 1) : mclamp c x = x := by
  unfold mclamp; rw [min_eq_left hx.2, max_eq_right hx.1]

theorem mclamp_cont (c : ℝ) : Continuous (mclamp c) := by unfold mclamp; fun_prop

theorem yC_cont (m k : ℝ) : Continuous (yC m k) := by unfold yC; fun_prop

/-- The integrand `gC` read through the clamp: continuous on the whole line. -/
noncomputable def mg (m k c x : ℝ) : ℝ := gC m k (mclamp c x)

/-- The time integrand `dt/dv = v² gC(v)` read through the clamp. -/
noncomputable def mph (m k c x : ℝ) : ℝ := mclamp c x ^ 2 * mg m k c x

/-- Cosmic time as a function of `v = √(a/a₀)` (`H₀ = a₀ = 1`), extended linearly-bounded off `[c, 1]`. -/
noncomputable def mtau (m k c v : ℝ) : ℝ := ∫ x in (0:ℝ)..v, mph m k c x

section
variable {m k c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hy : ∀ v ∈ Icc c 1, 0 < yC m k v)
include hc hc1 hy

theorem mg_cont : Continuous (mg m k c) := by
  unfold mg gC
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hp := hy _ (mclamp_mem hc1 x)
  apply ContinuousAt.div continuousAt_const
  · exact ((yC_cont m k).comp (mclamp_cont c)).continuousAt.sqrt
  · exact (Real.sqrt_pos.2 hp).ne'

theorem mph_cont : Continuous (mph m k c) := by
  unfold mph
  exact ((mclamp_cont c).pow 2).mul (mg_cont hc hc1 hy)

/-- A uniform positive lower bound of the time integrand. -/
theorem mph_lower : ∃ δ : ℝ, 0 < δ ∧ ∀ x, δ ≤ mph m k c x := by
  set B : ℝ := |m| + |k| + |1 - m - k| + 1 with hB
  have hB0 : 0 < B := by positivity
  refine ⟨c ^ 2 * (2 / √B), by positivity, fun x => ?_⟩
  have hmem := mclamp_mem hc1 x
  set v := mclamp c x with hv
  have hv0 : 0 ≤ v := le_trans hc.le hmem.1
  have hv1 : v ≤ 1 := hmem.2
  have hp := hy v hmem
  have hv2 : v ^ 2 ≤ 1 := pow_le_one₀ hv0 hv1
  have hv6 : v ^ 6 ≤ 1 := pow_le_one₀ hv0 hv1
  have hyB : yC m k v ≤ B := by
    unfold yC
    have e1 : k * v ^ 2 ≤ |k| := by
      calc k * v ^ 2 ≤ |k| * v ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self k) (by positivity)
        _ ≤ |k| * 1 := mul_le_mul_of_nonneg_left hv2 (abs_nonneg k)
        _ = |k| := mul_one _
    have e2 : (1 - m - k) * v ^ 6 ≤ |1 - m - k| := by
      calc (1 - m - k) * v ^ 6 ≤ |1 - m - k| * v ^ 6 :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ ≤ |1 - m - k| * 1 := mul_le_mul_of_nonneg_left hv6 (abs_nonneg _)
        _ = |1 - m - k| := mul_one _
    linarith [le_abs_self m]
  have hs : √(yC m k v) ≤ √B := Real.sqrt_le_sqrt hyB
  have hsp : 0 < √(yC m k v) := Real.sqrt_pos.2 hp
  have hg : 2 / √B ≤ mg m k c x := by
    unfold mg gC; rw [← hv]
    exact div_le_div_of_nonneg_left (by norm_num) hsp hs
  have hcv : c ^ 2 ≤ v ^ 2 := pow_le_pow_left₀ hc.le hmem.1 2
  unfold mph; rw [← hv]
  exact mul_le_mul hcv hg (by positivity) (by positivity)

theorem mtau_deriv (x : ℝ) : HasDerivAt (mtau m k c) (mph m k c x) x :=
  ((mph_cont hc hc1 hy).integral_hasStrictDerivAt 0 x).hasDerivAt

theorem mtau_strictMono : StrictMono (mtau m k c) := by
  obtain ⟨δ, hδ, hle⟩ := mph_lower hc hc1 hy
  apply strictMono_of_deriv_pos
  intro x
  rw [(mtau_deriv hc hc1 hy x).deriv]
  exact lt_of_lt_of_le hδ (hle x)

theorem mtau_surj : Function.Surjective (mtau m k c) := by
  obtain ⟨δ, hδ, hle⟩ := mph_lower hc hc1 hy
  have hdiff : Differentiable ℝ (mtau m k c) := fun x => (mtau_deriv hc hc1 hy x).differentiableAt
  have hcont : Continuous (mtau m k c) := hdiff.continuous
  have h0 : mtau m k c 0 = 0 := by simp [mtau]
  -- `mtau − δ x` is monotone
  have hmono : Monotone (fun x => mtau m k c x - δ * x) := by
    apply monotone_of_deriv_nonneg (hdiff.sub (by fun_prop))
    intro x
    have hd : HasDerivAt (fun x => mtau m k c x - δ * x) (mph m k c x - δ * 1) x :=
      (mtau_deriv hc hc1 hy x).sub ((hasDerivAt_id x).const_mul δ)
    show 0 ≤ deriv (fun x => mtau m k c x - δ * x) x
    rw [hd.deriv]
    linarith [hle x]
  intro y
  set R := |y| / δ with hR
  have hR0 : 0 ≤ R := by positivity
  have hup : |y| ≤ mtau m k c R := by
    have := hmono hR0
    simp only [h0, mul_zero, sub_zero] at this
    have e : δ * R = |y| := by rw [hR]; field_simp
    linarith
  have hlo : mtau m k c (-R) ≤ -|y| := by
    have := hmono (show -R ≤ 0 by linarith)
    simp only [h0, mul_zero, sub_zero] at this
    have e : δ * R = |y| := by rw [hR]; field_simp
    linarith
  have hyI : y ∈ Icc (mtau m k c (-R)) (mtau m k c R) :=
    ⟨by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩
  obtain ⟨x, -, hx⟩ := intermediate_value_Icc (by linarith) hcont.continuousOn hyI
  exact ⟨x, hx⟩

end

/-- A scale factor of the ΛCDM family with curvature: `a = V²` with `V` the inverse of `mtau`. -/
noncomputable def mV (m k c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) (hy : ∀ v ∈ Icc c 1, 0 < yC m k v) :
    ℝ → ℝ :=
  (StrictMono.orderIsoOfSurjective (mtau m k c) (mtau_strictMono hc hc1 hy)
    (mtau_surj hc hc1 hy)).symm

section
variable {m k c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hy : ∀ v ∈ Icc c 1, 0 < yC m k v)
include hc hc1 hy

theorem mV_tau (v : ℝ) : mV m k c hc hc1 hy (mtau m k c v) = v := by
  unfold mV
  exact StrictMono.orderIsoOfSurjective_symm_apply_self _ _ _ v

theorem tau_mV (t : ℝ) : mtau m k c (mV m k c hc hc1 hy t) = t := by
  unfold mV
  exact (StrictMono.orderIsoOfSurjective (mtau m k c) (mtau_strictMono hc hc1 hy)
    (mtau_surj hc hc1 hy)).apply_symm_apply t

theorem mV_mono : Monotone (mV m k c hc hc1 hy) := by
  unfold mV; exact OrderIso.monotone _

theorem mV_cont : Continuous (mV m k c hc hc1 hy) := by
  unfold mV; exact OrderIso.continuous _

theorem mV_deriv (t : ℝ) :
    HasDerivAt (mV m k c hc hc1 hy) (mph m k c (mV m k c hc hc1 hy t))⁻¹ t := by
  obtain ⟨δ, hδ, hle⟩ := mph_lower hc hc1 hy
  apply HasDerivAt.of_local_left_inverse (mV_cont hc hc1 hy).continuousAt
    (mtau_deriv hc hc1 hy _)
  · exact (lt_of_lt_of_le hδ (hle _)).ne'
  · exact Filter.Eventually.of_forall (tau_mV hc hc1 hy)

theorem mV_mem {s : ℝ} (hs : s ∈ Icc (mtau m k c c) (mtau m k c 1)) : mV m k c hc hc1 hy s ∈ Icc c 1 := by
  have h1 := mV_mono hc hc1 hy hs.1
  have h2 := mV_mono hc hc1 hy hs.2
  rw [mV_tau] at h1 h2
  exact ⟨h1, h2⟩

theorem mg_eq {v : ℝ} (hv : v ∈ Icc c 1) : mg m k c v = gC m k v := by
  unfold mg; rw [mclamp_eq hv]

theorem mph_eq {v : ℝ} (hv : v ∈ Icc c 1) : mph m k c v = v ^ 2 * gC m k v := by
  unfold mph; rw [mclamp_eq hv, mg_eq hc hc1 hy hv]

end

/-- The scale factor `a = V²`. -/
noncomputable def ma (m k c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) (hy : ∀ v ∈ Icc c 1, 0 < yC m k v) :
    ℝ → ℝ := fun t => mV m k c hc hc1 hy t ^ 2

section
variable {m k c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hy : ∀ v ∈ Icc c 1, 0 < yC m k v)
include hc hc1 hy

theorem ma_deriv (t : ℝ) : HasDerivAt (ma m k c hc hc1 hy)
    (2 * mV m k c hc hc1 hy t * (mph m k c (mV m k c hc hc1 hy t))⁻¹) t := by
  have := (mV_deriv hc hc1 hy t).pow 2
  unfold ma
  convert this using 1
  simp

theorem ma_tau {w : ℝ} : ma m k c hc hc1 hy (mtau m k c w) = w ^ 2 := by
  unfold ma; rw [mV_tau]

/-- On the interval where `V ∈ [c, 1]`: `H = √y(V)/V³`. -/
theorem ma_hubble {s : ℝ} (hs : s ∈ Icc (mtau m k c c) (mtau m k c 1)) :
    hubble (ma m k c hc hc1 hy) s
      = √(yC m k (mV m k c hc hc1 hy s)) / mV m k c hc hc1 hy s ^ 3 := by
  have hmem := mV_mem hc hc1 hy hs
  set V := mV m k c hc hc1 hy s with hV
  have hV0 : 0 < V := lt_of_lt_of_le hc hmem.1
  have hp := hy V hmem
  have hsq : 0 < √(yC m k V) := Real.sqrt_pos.2 hp
  unfold hubble
  rw [(ma_deriv hc hc1 hy s).deriv, mph_eq hc hc1 hy hmem]
  unfold ma gC
  rw [← hV]
  field_simp

theorem ma_hubble0 : hubble (ma m k c hc hc1 hy) (mtau m k c 1) = 1 := by
  have hs : mtau m k c 1 ∈ Icc (mtau m k c c) (mtau m k c 1) :=
    ⟨(mtau_strictMono hc hc1 hy).monotone hc1, le_rfl⟩
  rw [ma_hubble hc hc1 hy hs, mV_tau]
  simp [yC]

theorem ma_pos {s : ℝ} (hs : s ∈ Icc (mtau m k c c) (mtau m k c 1)) :
    0 < ma m k c hc hc1 hy s := by
  have hmem := mV_mem hc hc1 hy hs
  unfold ma; have : 0 < mV m k c hc hc1 hy s := lt_of_lt_of_le hc hmem.1
  positivity

/-- The curved ΛCDM law in redshift form, `H₀ = 1`, `a₀ = 1`. -/
theorem ma_law {s : ℝ} (hs : s ∈ Icc (mtau m k c c) (mtau m k c 1)) :
    hubble (ma m k c hc hc1 hy) s = hubble (ma m k c hc hc1 hy) (mtau m k c 1) *
      √(m * (1 + redshift (ma m k c hc hc1 hy) (mtau m k c 1) s) ^ 3
        + k * (1 + redshift (ma m k c hc hc1 hy) (mtau m k c 1) s) ^ 2 + (1 - k) - m) := by
  have hmem := mV_mem hc hc1 hy hs
  have hV0 : 0 < mV m k c hc hc1 hy s := lt_of_lt_of_le hc hmem.1
  rw [ma_hubble0, one_mul, ma_hubble hc hc1 hy hs]
  unfold redshift
  rw [ma_tau]
  have := sqrt_algC m k 1 (ma m k c hc hc1 hy s) (mV m k c hc hc1 hy s) hV0 one_pos
    (by unfold ma; ring) (hy _ hmem)
  rw [← this]; norm_num

/-- The comoving distance to `t = mtau w` is `∫_w^1 gC`. -/
theorem ma_comoving {w : ℝ} (hw : w ∈ Icc c 1) :
    comoving (ma m k c hc hc1 hy) (mtau m k c 1) (mtau m k c w) = ∫ v in w..1, gC m k v := by
  have hmono := (mtau_strictMono hc hc1 hy).monotone
  have hwt : mtau m k c w ≤ mtau m k c 1 := hmono hw.2
  have hsub : ∀ s ∈ uIcc (mtau m k c w) (mtau m k c 1), s ∈ Icc (mtau m k c c) (mtau m k c 1) := by
    intro s hs; rw [uIcc_of_le hwt] at hs; exact ⟨le_trans (hmono hw.1) hs.1, hs.2⟩
  set G : ℝ → ℝ := fun x => ∫ v in (1:ℝ)..x, mg m k c v with hG
  have hGd : ∀ x, HasDerivAt G (mg m k c x) x := fun x =>
    ((mg_cont hc hc1 hy).integral_hasStrictDerivAt 1 x).hasDerivAt
  set F : ℝ → ℝ := fun s => G (mV m k c hc hc1 hy s) with hF
  have hFd : ∀ s ∈ uIcc (mtau m k c w) (mtau m k c 1), HasDerivAt F (1 / ma m k c hc hc1 hy s) s := by
    intro s hs
    have hmem := mV_mem hc hc1 hy (hsub s hs)
    have hV0 : 0 < mV m k c hc hc1 hy s := lt_of_lt_of_le hc hmem.1
    have hc' : HasDerivAt F _ s := (hGd (mV m k c hc hc1 hy s)).comp s (mV_deriv hc hc1 hy s)
    convert hc' using 1
    rw [mph_eq hc hc1 hy hmem, mg_eq hc hc1 hy hmem]
    have hg : 0 < gC m k (mV m k c hc hc1 hy s) := by
      unfold gC; have := Real.sqrt_pos.2 (hy _ hmem); positivity
    unfold ma; field_simp
  have hint : IntervalIntegrable (fun s => 1 / ma m k c hc hc1 hy s) volume
      (mtau m k c w) (mtau m k c 1) := by
    apply ContinuousOn.intervalIntegrable
    intro s hs
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_const.div
    · exact ((mV_cont hc hc1 hy).pow 2).continuousAt
    · exact (ma_pos hc hc1 hy (hsub s hs)).ne'
  unfold comoving
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hFd hint]
  simp only [hF, hG, mV_tau]
  rw [intervalIntegral.integral_same, zero_sub, intervalIntegral.integral_symm w 1, neg_neg]
  apply intervalIntegral.integral_congr
  intro v hv
  rw [uIcc_of_le hw.2] at hv
  exact mg_eq hc hc1 hy ⟨le_trans hw.1 hv.1, hv.2⟩

end

/-! ## A closed model: matter density one half, total density two (curvature constant one) -/

/-- `y = 1/2 − v² + (3/2) v⁶` stays above `0.1764` while `v² ≤ 1`. -/
theorem y2_lower (v : ℝ) (hv : v ^ 2 ≤ 1) : 441 / 2500 ≤ yC (1 / 2) (-1) v := by
  unfold yC
  set x := v ^ 2 with hx
  have hx0 : 0 ≤ x := sq_nonneg v
  have e : (1 / 2 : ℝ) + -1 * v ^ 2 + (1 - 1 / 2 - -1) * v ^ 6 = 1 / 2 - x + 3 / 2 * x ^ 3 := by
    rw [hx]; ring
  rw [e]
  nlinarith [mul_nonneg (sq_nonneg (x - 47 / 100)) (show (0:ℝ) ≤ x + 94 / 100 by linarith)]

theorem y2_pos (v : ℝ) (hv : v ^ 2 ≤ 1) : 0 < yC (1 / 2) (-1) v :=
  lt_of_lt_of_le (by norm_num) (y2_lower v hv)

/-- On `[0.59, 0.79]` the integrand is at least four (`y ≤ 1/4`). -/
theorem g2_lo4 (v : ℝ) (h1 : 59 / 100 ≤ v) (h2 : v ≤ 79 / 100) : 4 ≤ gC (1 / 2) (-1) v := by
  have hv2 : v ^ 2 ≤ 1 := by nlinarith
  have hp := y2_pos v hv2
  have hy : yC (1 / 2) (-1) v ≤ 1 / 4 := by
    unfold yC
    set x := v ^ 2 with hx
    have hxl : 3481 / 10000 ≤ x := by nlinarith
    have hxu : x ≤ 6241 / 10000 := by nlinarith
    have e : (1 / 2 : ℝ) + -1 * v ^ 2 + (1 - 1 / 2 - -1) * v ^ 6 = 1 / 2 - x + 3 / 2 * x ^ 3 := by
      rw [hx]; ring
    rw [e]
    nlinarith [mul_nonneg (sub_nonneg.2 hxl) (sub_nonneg.2 hxu),
      mul_nonneg (mul_nonneg (sub_nonneg.2 hxl) (sub_nonneg.2 hxu)) (show (0:ℝ) ≤ x by linarith)]
  have hs : √(yC (1 / 2) (-1) v) ≤ 1 / 2 :=
    (Real.sqrt_le_sqrt hy).trans_eq
      (by rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)])
  unfold gC
  rw [le_div_iff₀ (Real.sqrt_pos.2 hp)]; linarith

/-- On `[0, 1]` the integrand is at least two (`y ≤ 1`). -/
theorem g2_lo2 (v : ℝ) (h0 : 0 ≤ v) (h2 : v ≤ 1) : 2 ≤ gC (1 / 2) (-1) v := by
  have hv2 : v ^ 2 ≤ 1 := by nlinarith
  have hp := y2_pos v hv2
  have hy : yC (1 / 2) (-1) v ≤ 1 := by
    unfold yC
    have h6 : v ^ 6 ≤ v ^ 2 := by
      have : v ^ 6 = v ^ 2 * (v ^ 2) ^ 2 := by ring
      rw [this]; nlinarith [sq_nonneg v, pow_le_one₀ (n := 2) (sq_nonneg v) hv2]
    nlinarith
  have hs : √(yC (1 / 2) (-1) v) ≤ 1 := (Real.sqrt_le_sqrt hy).trans_eq Real.sqrt_one
  unfold gC
  rw [le_div_iff₀ (Real.sqrt_pos.2 hp)]; linarith

/-- On `[0, 1]` the integrand is at most `2/0.42`. -/
theorem g2_up (v : ℝ) (h0 : 0 ≤ v) (h2 : v ≤ 1) : gC (1 / 2) (-1) v ≤ 2 / (42 / 100) := by
  have hv2 : v ^ 2 ≤ 1 := by nlinarith
  have hl := y2_lower v hv2
  have hs : 42 / 100 ≤ √(yC (1 / 2) (-1) v) := Real.le_sqrt_of_sq_le (by norm_num; linarith)
  unfold gC
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs

theorem g2_cont : ContinuousOn (gC (1 / 2) (-1)) (Icc 0 1) := by
  intro v hv
  have hp := y2_pos v (by nlinarith [hv.1, hv.2])
  apply ContinuousAt.continuousWithinAt
  apply continuousAt_const.div
  · exact (yC_cont _ _).continuousAt.sqrt
  · exact (Real.sqrt_pos.2 hp).ne'

theorem g2_int {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ 1) :
    IntervalIntegrable (gC (1 / 2) (-1)) volume α β :=
  (g2_cont.mono (Icc_subset_Icc hα hβ)).intervalIntegrable_of_Icc hαβ

theorem J2_lower {α β : ℝ} (lo : ℝ) (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ 1)
    (hlo : ∀ v ∈ Icc α β, lo ≤ gC (1 / 2) (-1) v) :
    lo * (β - α) ≤ ∫ v in α..β, gC (1 / 2) (-1) v := by
  have := intervalIntegral.integral_mono_on hαβ intervalIntegrable_const (g2_int hα hαβ hβ) hlo
  simpa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using this

theorem J2_upper {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ 1) :
    ∫ v in α..β, gC (1 / 2) (-1) v ≤ 2 / (42 / 100) * (β - α) := by
  have := intervalIntegral.integral_mono_on hαβ (g2_int hα hαβ hβ) intervalIntegrable_const
    (fun v hv => g2_up v (le_trans hα hv.1) (le_trans hv.2 hβ))
  rw [intervalIntegral.integral_const, smul_eq_mul] at this
  linarith

/-- The quartic at the two redshifts: both positive, and `Q(x₃) ≤ 0.42 Q(x₅)`, for the SNe + quasar fit. -/
theorem q_sq (L : ℝ) (hL1 : 30101 / 100000 ≤ L) (hL2 : L ≤ 30105 / 100000) :
    0 < 3 / 2 * L + 3.075 * (3 / 2 * L) ^ 2 + 4.466 * (3 / 2 * L) ^ 3 + (-3.716) * (3 / 2 * L) ^ 4 ∧
    3 / 2 * L + 3.075 * (3 / 2 * L) ^ 2 + 4.466 * (3 / 2 * L) ^ 3 + (-3.716) * (3 / 2 * L) ^ 4
      ≤ 21 / 50 * (5 / 2 * L + 3.075 * (5 / 2 * L) ^ 2 + 4.466 * (5 / 2 * L) ^ 3
        + (-3.716) * (5 / 2 * L) ^ 4) := by
  have hL0 : 0 < L := by linarith
  have l2a : (30101 / 100000) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by norm_num) hL1 2
  have l2b : L ^ 2 ≤ (30105 / 100000) ^ 2 := pow_le_pow_left₀ hL0.le hL2 2
  have l3a : (30101 / 100000) ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ (by norm_num) hL1 3
  have l3b : L ^ 3 ≤ (30105 / 100000) ^ 3 := pow_le_pow_left₀ hL0.le hL2 3
  constructor
  · have hG : 0 < 1 + 3.075 * (3 / 2 * L) + 4.466 * (3 / 2) ^ 2 * L ^ 2 - 3.716 * (3 / 2) ^ 3 * L ^ 3 := by
      norm_num at l2a l2b l3a l3b ⊢; linarith
    have e : 3 / 2 * L + 3.075 * (3 / 2 * L) ^ 2 + 4.466 * (3 / 2 * L) ^ 3 + (-3.716) * (3 / 2 * L) ^ 4
        = 3 / 2 * L * (1 + 3.075 * (3 / 2 * L) + 4.466 * (3 / 2) ^ 2 * L ^ 2 - 3.716 * (3 / 2) ^ 3 * L ^ 3) := by
      ring
    rw [e]; positivity
  · have hF : 0 < (21 / 50 * (5 / 2) - 3 / 2) + 3.075 * (21 / 50 * (5 / 2) ^ 2 - (3 / 2) ^ 2) * L
        + 4.466 * (21 / 50 * (5 / 2) ^ 3 - (3 / 2) ^ 3) * L ^ 2
        + (-3.716) * (21 / 50 * (5 / 2) ^ 4 - (3 / 2) ^ 4) * L ^ 3 := by
      norm_num at l2a l2b l3a l3b ⊢; linarith
    have e : 21 / 50 * (5 / 2 * L + 3.075 * (5 / 2 * L) ^ 2 + 4.466 * (5 / 2 * L) ^ 3 + (-3.716) * (5 / 2 * L) ^ 4)
        - (3 / 2 * L + 3.075 * (3 / 2 * L) ^ 2 + 4.466 * (3 / 2 * L) ^ 3 + (-3.716) * (3 / 2 * L) ^ 4)
        = L * ((21 / 50 * (5 / 2) - 3 / 2) + 3.075 * (21 / 50 * (5 / 2) ^ 2 - (3 / 2) ^ 2) * L
        + 4.466 * (21 / 50 * (5 / 2) ^ 3 - (3 / 2) ^ 3) * L ^ 2
        + (-3.716) * (21 / 50 * (5 / 2) ^ 4 - (3 / 2) ^ 4) * L ^ 3) := by ring
    nlinarith [mul_pos hL0 hF]

/-- The same for the SNe + GRB + quasar fit. -/
theorem q_sqg (L : ℝ) (hL1 : 30101 / 100000 ≤ L) (hL2 : L ≤ 30105 / 100000) :
    0 < 3 / 2 * L + 3.205 * (3 / 2 * L) ^ 2 + 3.564 * (3 / 2 * L) ^ 3 + (-2.510) * (3 / 2 * L) ^ 4 ∧
    3 / 2 * L + 3.205 * (3 / 2 * L) ^ 2 + 3.564 * (3 / 2 * L) ^ 3 + (-2.510) * (3 / 2 * L) ^ 4
      ≤ 21 / 50 * (5 / 2 * L + 3.205 * (5 / 2 * L) ^ 2 + 3.564 * (5 / 2 * L) ^ 3
        + (-2.510) * (5 / 2 * L) ^ 4) := by
  have hL0 : 0 < L := by linarith
  have l2a : (30101 / 100000) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by norm_num) hL1 2
  have l2b : L ^ 2 ≤ (30105 / 100000) ^ 2 := pow_le_pow_left₀ hL0.le hL2 2
  have l3a : (30101 / 100000) ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ (by norm_num) hL1 3
  have l3b : L ^ 3 ≤ (30105 / 100000) ^ 3 := pow_le_pow_left₀ hL0.le hL2 3
  constructor
  · have hG : 0 < 1 + 3.205 * (3 / 2 * L) + 3.564 * (3 / 2) ^ 2 * L ^ 2 - 2.510 * (3 / 2) ^ 3 * L ^ 3 := by
      norm_num at l2a l2b l3a l3b ⊢; linarith
    have e : 3 / 2 * L + 3.205 * (3 / 2 * L) ^ 2 + 3.564 * (3 / 2 * L) ^ 3 + (-2.510) * (3 / 2 * L) ^ 4
        = 3 / 2 * L * (1 + 3.205 * (3 / 2 * L) + 3.564 * (3 / 2) ^ 2 * L ^ 2 - 2.510 * (3 / 2) ^ 3 * L ^ 3) := by
      ring
    rw [e]; positivity
  · have hF : 0 < (21 / 50 * (5 / 2) - 3 / 2) + 3.205 * (21 / 50 * (5 / 2) ^ 2 - (3 / 2) ^ 2) * L
        + 3.564 * (21 / 50 * (5 / 2) ^ 3 - (3 / 2) ^ 3) * L ^ 2
        + (-2.510) * (21 / 50 * (5 / 2) ^ 4 - (3 / 2) ^ 4) * L ^ 3 := by
      norm_num at l2a l2b l3a l3b ⊢; linarith
    have e : 21 / 50 * (5 / 2 * L + 3.205 * (5 / 2 * L) ^ 2 + 3.564 * (5 / 2 * L) ^ 3 + (-2.510) * (5 / 2 * L) ^ 4)
        - (3 / 2 * L + 3.205 * (3 / 2 * L) ^ 2 + 3.564 * (3 / 2 * L) ^ 3 + (-2.510) * (3 / 2 * L) ^ 4)
        = L * ((21 / 50 * (5 / 2) - 3 / 2) + 3.205 * (21 / 50 * (5 / 2) ^ 2 - (3 / 2) ^ 2) * L
        + 3.564 * (21 / 50 * (5 / 2) ^ 3 - (3 / 2) ^ 3) * L ^ 2
        + (-2.510) * (21 / 50 * (5 / 2) ^ 4 - (3 / 2) ^ 4) * L ^ 3) := by ring
    nlinarith [mul_pos hL0 hF]

/-- The arithmetic of the last step: `0 < Q₃ ≤ 0.42 Q₅`, `0 < sin J₅ ≤ 1`, `sin J₃ ≥ 0.93` make the residual
at `4√2` at most the one at `2√2`. -/
theorem final_arith (s3 s5 Q3 Q5 l r : ℝ) (hl : 0 < l) (hr : 0 < r) (hQ3 : 0 < Q3)
    (hq : Q3 ≤ 21 / 50 * Q5) (h5p : 0 < s5) (h5u : s5 ≤ 1) (h3 : 93 / 100 ≤ s3) :
    5 * Real.logb 10 (4 * r * s5 / (l / 1 * Q5)) - 5 * Real.logb 10 (2 * r * s3 / (l / 1 * Q3)) ≤ 0 := by
  have hQ5 : 0 < Q5 := by linarith
  have hs3 : 0 < s3 := by linarith
  have hA : 0 < 4 * r * s5 / (l / 1 * Q5) := by positivity
  have hAB : 4 * r * s5 / (l / 1 * Q5) ≤ 2 * r * s3 / (l / 1 * Q3) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : s5 * Q3 ≤ 21 / 50 * Q5 := le_trans (mul_le_of_le_one_left hQ3.le h5u) hq
    have h2 : 93 / 100 * Q5 ≤ s3 * Q5 := mul_le_mul_of_nonneg_right h3 hQ5.le
    have hk : 0 ≤ r * l := by positivity
    have h3' := mul_le_mul_of_nonneg_left h1 hk
    have h4 := mul_le_mul_of_nonneg_left h2 hk
    have h5 : 0 ≤ r * l * Q5 := by positivity
    have e1 : 4 * r * s5 * (l / 1 * Q3) = 4 * (r * l * (s5 * Q3)) := by ring
    have e2 : 2 * r * s3 * (l / 1 * Q5) = 2 * (r * l * (s3 * Q5)) := by ring
    rw [e1, e2]
    nlinarith
  have := Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 10) hA hAB
  linarith

open Checked.Cosmography.B1Fit Checked.Cosmography.B1L19 Checked.Cosmography.Transverse in
/-- The closed model `Ω = 1/2`, `K = 1` (total density two): every hypothesis of the curved Lusso et al. 2019
headlines except the upper bound on the total density holds, and the residual at `1 + z = 4√2` does not exceed
the one at `1 + z = 2√2`, for any quartic whose values at the two redshifts satisfy `0 < Q₃ ≤ 0.42 Q₅`. -/
theorem closed2_core (a₂ a₃ a₄ : ℝ)
    (hQ3 : 0 < 3 / 2 * (Real.log 2 / Real.log 10) + a₂ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + a₃ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3 + a₄ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4)
    (hq : 3 / 2 * (Real.log 2 / Real.log 10) + a₂ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + a₃ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3 + a₄ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4
      ≤ 21 / 50 * (5 / 2 * (Real.log 2 / Real.log 10) + a₂ * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + a₃ * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 3 + a₄ * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 4)) :
    ∃ a : ℝ → ℝ, ∃ t₅ t₃ t₀ : ℝ, t₅ ≤ t₃ ∧ t₃ ≤ t₀ ∧ (∀ s ∈ Icc t₅ t₀, 0 < a s) ∧
      (∀ s ∈ Icc t₅ t₀, DifferentiableAt ℝ a s) ∧ 0 < hubble a t₀ ∧ omega0 1 a t₀ = 2 ∧
      (∀ s ∈ Icc t₅ t₀, hubble a s = hubble a t₀ * √(1 / 2 * (1 + redshift a t₀ s) ^ 3
        + (1 - omega0 1 a t₀) * (1 + redshift a t₀ s) ^ 2 + omega0 1 a t₀ - 1 / 2)) ∧
      redshift a t₀ t₃ = 2 * √2 - 1 ∧ redshift a t₀ t₅ = 4 * √2 - 1 ∧
      5 * Real.logb 10 (lumDist 1 a t₀ t₅ / logPolyDL4 a₂ a₃ a₄ 1 (redshift a t₀ t₅))
        - 5 * Real.logb 10 (lumDist 1 a t₀ t₃ / logPolyDL4 a₂ a₃ a₄ 1 (redshift a t₀ t₃)) ≤ 0 := by
  obtain ⟨hq2l, hq2u⟩ := sqrt2_bounds
  have hs3 : (1:ℝ) < 2 * √2 := by linarith
  have hs5 : (1:ℝ) < 4 * √2 := by linarith
  obtain ⟨hw3p, hw3⟩ := w_lt_one _ hs3
  obtain ⟨hw5p, hw5⟩ := w_lt_one _ hs5
  obtain ⟨wb3u, wb3l⟩ := wb (2 * √2) (148651 / 250000) (594603 / 1000000) (by positivity)
    (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  obtain ⟨wb5u, wb5l⟩ := wb (4 * √2) (420449 / 1000000) (13139 / 31250) (by positivity)
    (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  set c := √(1 / (4 * √2)) with hcdef
  set w := √(1 / (2 * √2)) with hwdef
  have hc1 : c ≤ 1 := hw5.le
  have hy : ∀ v ∈ Icc c 1, 0 < yC (1 / 2) (-1) v := fun v hv =>
    y2_pos v (by nlinarith [hv.1, hv.2])
  have hcw : c ≤ w := by linarith
  have hwm : w ∈ Icc c 1 := ⟨hcw, hw3.le⟩
  have hcm : c ∈ Icc c 1 := ⟨le_rfl, hc1⟩
  set a := ma (1 / 2) (-1) c hw5p hc1 hy with hadef
  have hmono := (mtau_strictMono hw5p hc1 hy).monotone
  set T := mtau (1 / 2) (-1) c with hTdef
  have hIcc : ∀ s ∈ Icc (T c) (T 1), s ∈ Icc (mtau (1 / 2) (-1) c c) (mtau (1 / 2) (-1) c 1) :=
    fun s hs => hs
  have ha0 : a (T 1) = 1 := by rw [hadef, ma_tau]; norm_num
  have hH0 : hubble a (T 1) = 1 := ma_hubble0 hw5p hc1 hy
  have hom : omega0 1 a (T 1) = 2 := by unfold omega0; rw [hH0, ha0]; norm_num
  have hz : ∀ v ∈ Icc c 1, ∀ r : ℝ, 0 < r → v = √(1 / r) → redshift a (T 1) (T v) = r - 1 := by
    intro v hv r hr hvr
    unfold redshift; rw [ha0, hadef, ma_tau, hvr, Real.sq_sqrt (by positivity)]; field_simp
  have hz3 := hz w hwm (2 * √2) (by positivity) rfl
  have hz5 := hz c hcm (4 * √2) (by positivity) rfl
  refine ⟨a, T c, T w, T 1, hmono hcw, hmono hw3.le, fun s hs => ma_pos hw5p hc1 hy (hIcc s hs),
    fun s hs => (ma_deriv hw5p hc1 hy s).differentiableAt, by rw [hH0]; norm_num, hom, ?_, hz3, hz5, ?_⟩
  · intro s hs
    rw [ma_law hw5p hc1 hy (hIcc s hs), hom]
    congr 2; ring
  -- distances
  set J3 := ∫ v in w..1, gC (1 / 2) (-1) v with hJ3
  set J5 := ∫ v in c..1, gC (1 / 2) (-1) v with hJ5
  have hχ3 : comoving a (T 1) (T w) = J3 := ma_comoving hw5p hc1 hy hwm
  have hχ5 : comoving a (T 1) (T c) = J5 := ma_comoving hw5p hc1 hy hcm
  have hd3 : lumDist 1 a (T 1) (T w) = 2 * √2 * Real.sin J3 := by
    unfold lumDist transverse; rw [ha0, hz3, hχ3]; simp
  have hd5 : lumDist 1 a (T 1) (T c) = 4 * √2 * Real.sin J5 := by
    unfold lumDist transverse; rw [ha0, hz5, hχ5]; simp
  -- integral bounds
  have hJ3lo : 12015 / 10000 ≤ J3 := by
    have i1 := g2_int (α := w) (β := 79 / 100) (by linarith) (by linarith) (by norm_num)
    have i2 := g2_int (α := 79 / 100) (β := 1) (by norm_num) (by norm_num) le_rfl
    rw [hJ3, ← intervalIntegral.integral_add_adjacent_intervals i1 i2]
    have b1 := J2_lower (α := w) (β := 79 / 100) 4 (by linarith) (by linarith) (by norm_num)
      (fun v hv => g2_lo4 v (by linarith [hv.1]) hv.2)
    have b2 := J2_lower (α := 79 / 100) (β := 1) 2 (by norm_num) (by norm_num) le_rfl
      (fun v hv => g2_lo2 v (by linarith [hv.1]) hv.2)
    linarith
  have hJ3up : J3 ≤ 19306 / 10000 := by
    have := J2_upper (α := w) (β := 1) (by linarith) hw3.le le_rfl
    rw [← hJ3] at this; linarith
  have hJ5up : J5 ≤ 276 / 100 := by
    have := J2_upper (α := c) (β := 1) (by linarith) hc1 le_rfl
    rw [← hJ5] at this; norm_num at this ⊢; linarith
  have hJ53 : J3 ≤ J5 := by
    have i1 := g2_int (α := c) (β := w) (by linarith) hcw (by linarith)
    have i2 := g2_int (α := w) (β := 1) (by linarith) hw3.le le_rfl
    rw [hJ5, ← intervalIntegral.integral_add_adjacent_intervals i1 i2, ← hJ3]
    have : 0 ≤ ∫ v in c..w, gC (1 / 2) (-1) v :=
      intervalIntegral.integral_nonneg hcw (fun v _ => gC_nonneg _ _ v)
    linarith
  have hpi1 := Real.pi_gt_d2
  have hpi2 := Real.pi_lt_d2
  have hsin5p : 0 < Real.sin J5 := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hsin5u : Real.sin J5 ≤ 1 := Real.sin_le_one J5
  have hsin3 : 93 / 100 ≤ Real.sin J3 := by
    rw [← Real.cos_sub_pi_div_two]
    have hc := Real.one_sub_sq_div_two_le_cos (x := J3 - π / 2)
    have hx1 : -(3736 / 10000) ≤ J3 - π / 2 := by linarith
    have hx2 : J3 - π / 2 ≤ 3736 / 10000 := by linarith
    nlinarith
  -- the residual difference
  rw [hz3, hz5, lp4_eq a₂ a₃ a₄ 1 _ _ x3_eq, lp4_eq a₂ a₃ a₄ 1 _ _ x5_eq, hd3, hd5]
  exact final_arith _ _ _ _ _ _ (Real.log_pos (by norm_num)) (by linarith) hQ3 hq hsin5p hsin5u hsin3

open Checked.Cosmography.B1L19 in
/-- `l19_sq_curved` without `Ω₀ ≤ 11/10`: the closed model of matter density one half and total density two
(curvature constant one); the residual of the SNe + quasar central fit does not grow between `1 + z = 2√2`
and `4√2`. -/
theorem l19_sq_curved_h9 : necessity% Checked.Cosmography.B1L19Curved.l19_sq_curved 9 := by
  obtain ⟨l1, l2⟩ := L_bounds
  obtain ⟨hQ3, hq⟩ := q_sq _ l1 l2
  obtain ⟨a, t₅, t₃, t₀, h53, h30, hp, hd, hH₀, hom, hH, hz3, hz5, hres⟩ := closed2_core _ _ _ hQ3 hq
  refine ⟨1 / 2, 1, by norm_num, by norm_num, a, t₅, t₃, t₀, h53, h30, hp, hd, hH₀,
    by rw [hom]; norm_num, hH, hz3, hz5, 1, one_pos, ?_⟩
  rw [not_lt]; linarith

open Checked.Cosmography.B1L19 in
/-- `l19_sqg_curved` without `Ω₀ ≤ 11/10`: the same closed model; the residual of the SNe + GRB + quasar
central fit does not grow between `1 + z = 2√2` and `4√2`. -/
theorem l19_sqg_curved_h9 : necessity% Checked.Cosmography.B1L19Curved.l19_sqg_curved 9 := by
  obtain ⟨l1, l2⟩ := L_bounds
  obtain ⟨hQ3, hq⟩ := q_sqg _ l1 l2
  obtain ⟨a, t₅, t₃, t₀, h53, h30, hp, hd, hH₀, hom, hH, hz3, hz5, hres⟩ := closed2_core _ _ _ hQ3 hq
  refine ⟨1 / 2, 1, by norm_num, by norm_num, a, t₅, t₃, t₀, h53, h30, hp, hd, hH₀,
    by rw [hom]; norm_num, hH, hz3, hz5, 1, one_pos, ?_⟩
  rw [not_lt]; linarith

/-! ## Flat models at any matter density: step bounds of `∫ gC m 0` (integrand decreasing for `m ≤ 1`) -/

theorem fy_pos {m : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1) (v : ℝ) : 0 < yC m 0 v := by
  unfold yC; have : 0 ≤ (1 - m - 0) * v ^ 6 := mul_nonneg (by linarith) (by positivity)
  linarith

theorem fy_mono {m : ℝ} (hm1 : m ≤ 1) {v w : ℝ} (hv : 0 ≤ v) (hvw : v ≤ w) :
    yC m 0 v ≤ yC m 0 w := by
  unfold yC
  have : v ^ 6 ≤ w ^ 6 := pow_le_pow_left₀ hv hvw 6
  nlinarith

theorem fg_cont {m : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1) : Continuous (gC m 0) := by
  unfold gC
  refine continuous_iff_continuousAt.2 fun v => ?_
  apply continuousAt_const.div ((yC_cont m 0).continuousAt.sqrt)
  exact (Real.sqrt_pos.2 (fy_pos hm0 hm1 v)).ne'

theorem fpiece_lo (m p q c : ℝ) (hm0 : 0 < m) (hm1 : m ≤ 1) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 1)
    (hc : 0 < c) (h : yC m 0 q ≤ (2 / c) ^ 2) : (q - p) * c ≤ ∫ v in p..q, gC m 0 v := by
  have hb : ∀ v ∈ Icc p q, c ≤ gC m 0 v := by
    intro v hv
    have hy := fy_pos hm0 hm1 v
    have hs : √(yC m 0 v) ≤ 2 / c :=
      (Real.sqrt_le_sqrt (le_trans (fy_mono hm1 (le_trans hp hv.1) hv.2) h)).trans_eq
        (Real.sqrt_sq (by positivity))
    unfold gC
    rw [le_div_iff₀ (Real.sqrt_pos.2 hy)]
    calc c * √(yC m 0 v) ≤ c * (2 / c) := mul_le_mul_of_nonneg_left hs hc.le
      _ = 2 := by field_simp
  have := intervalIntegral.integral_mono_on hpq intervalIntegrable_const
    ((fg_cont hm0 hm1).intervalIntegrable (μ := volume) p q) hb
  rw [intervalIntegral.integral_const, smul_eq_mul] at this
  linarith

theorem fpiece_up (m p q c : ℝ) (hm0 : 0 < m) (hm1 : m ≤ 1) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 1)
    (hc : 0 < c) (h : (2 / c) ^ 2 ≤ yC m 0 p) : ∫ v in p..q, gC m 0 v ≤ (q - p) * c := by
  have hb : ∀ v ∈ Icc p q, gC m 0 v ≤ c := by
    intro v hv
    have hs : 2 / c ≤ √(yC m 0 v) :=
      (Real.sqrt_sq (by positivity : (0:ℝ) ≤ 2 / c)).symm.trans_le
        (Real.sqrt_le_sqrt (le_trans h (fy_mono hm1 hp hv.1)))
    have hR : 0 < √(yC m 0 v) := lt_of_lt_of_le (by positivity) hs
    unfold gC
    rw [div_le_iff₀ hR]
    calc 2 = c * (2 / c) := by field_simp
      _ ≤ c * √(yC m 0 v) := mul_le_mul_of_nonneg_left hs hc.le
  have := intervalIntegral.integral_mono_on hpq ((fg_cont hm0 hm1).intervalIntegrable (μ := volume) p q)
    intervalIntegrable_const hb
  rw [intervalIntegral.integral_const, smul_eq_mul] at this
  linarith

theorem fsplit_lo (m : ℝ) (hm0 : 0 < m) (hm1 : m ≤ 1) (p q r : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q)
    (hqr : q ≤ r) (hr : r ≤ 1) {A B : ℝ} (h1 : A ≤ ∫ v in p..q, gC m 0 v)
    (h2 : B ≤ ∫ v in q..r, gC m 0 v) : A + B ≤ ∫ v in p..r, gC m 0 v := by
  rw [← intervalIntegral.integral_add_adjacent_intervals ((fg_cont hm0 hm1).intervalIntegrable (μ := volume) p q)
    ((fg_cont hm0 hm1).intervalIntegrable q r)]
  linarith

theorem fsplit_up (m : ℝ) (hm0 : 0 < m) (hm1 : m ≤ 1) (p q r : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q)
    (hqr : q ≤ r) (hr : r ≤ 1) {A B : ℝ} (h1 : ∫ v in p..q, gC m 0 v ≤ A)
    (h2 : ∫ v in q..r, gC m 0 v ≤ B) : ∫ v in p..r, gC m 0 v ≤ A + B := by
  rw [← intervalIntegral.integral_add_adjacent_intervals ((fg_cont hm0 hm1).intervalIntegrable (μ := volume) p q)
    ((fg_cont hm0 hm1).intervalIntegrable q r)]
  linarith

/-- Moving the lower end of `∫_w^1 gC m 0`: the integral decreases as `w` increases. -/
theorem fshift (m : ℝ) (hm0 : 0 < m) (hm1 : m ≤ 1) {w w' : ℝ} (hww : w ≤ w') :
    ∫ v in w'..1, gC m 0 v ≤ ∫ v in w..1, gC m 0 v := by
  rw [← intervalIntegral.integral_add_adjacent_intervals ((fg_cont hm0 hm1).intervalIntegrable w w')
    ((fg_cont hm0 hm1).intervalIntegrable w' 1)]
  have : 0 ≤ ∫ v in w..w', gC m 0 v := intervalIntegral.integral_nonneg hww (fun v _ => gC_nonneg _ _ v)
  linarith

theorem fJ1_lo : (17299219 / 50000000 : ℝ) ≤ ∫ v in (8409 / 10000 : ℝ)..1, gC (11 / 20 : ℝ) 0 v := by
  have h := (fsplit_lo (11 / 20 : ℝ) (by norm_num) (by norm_num) (8409 / 10000 : ℝ) (538 / 625 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fpiece_lo (11 / 20 : ℝ) (8409 / 10000 : ℝ) (538 / 625 : ℝ) (23359 / 10000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold yC; norm_num)) (fsplit_lo (11 / 20 : ℝ) (by norm_num) (by norm_num) (538 / 625 : ℝ) (8807 / 10000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fpiece_lo (11 / 20 : ℝ) (538 / 625 : ℝ) (8807 / 10000 : ℝ) (22941 / 10000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold yC; norm_num)) (fsplit_lo (11 / 20 : ℝ) (by norm_num) (by norm_num) (8807 / 10000 : ℝ) (4503 / 5000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fpiece_lo (11 / 20 : ℝ) (8807 / 10000 : ℝ) (4503 / 5000 : ℝ) (9 / 4 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold yC; norm_num)) (fsplit_lo (11 / 20 : ℝ) (by norm_num) (by norm_num) (4503 / 5000 : ℝ) (1841 / 2000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fpiece_lo (11 / 20 : ℝ) (4503 / 5000 : ℝ) (1841 / 2000 : ℝ) (4407 / 2000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold yC; norm_num)) (fsplit_lo (11 / 20 : ℝ) (by norm_num) (by norm_num) (1841 / 2000 : ℝ) (2351 / 2500 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fpiece_lo (11 / 20 : ℝ) (1841 / 2000 : ℝ) (2351 / 2500 : ℝ) (21551 / 10000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold yC; norm_num)) (fsplit_lo (11 / 20 : ℝ) (by norm_num) (by norm_num) (2351 / 2500 : ℝ) (9603 / 10000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fpiece_lo (11 / 20 : ℝ) (2351 / 2500 : ℝ) (9603 / 10000 : ℝ) (21047 / 10000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold yC; norm_num)) (fsplit_lo (11 / 20 : ℝ) (by norm_num) (by norm_num) (9603 / 10000 : ℝ) (4901 / 5000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fpiece_lo (11 / 20 : ℝ) (9603 / 10000 : ℝ) (4901 / 5000 : ℝ) (20529 / 10000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold yC; norm_num)) (fpiece_lo (11 / 20 : ℝ) (4901 / 5000 : ℝ) (1 : ℝ) (2 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold yC; norm_num)))))))))
  norm_num at h ⊢; linarith

theorem fJ1_up : ∫ v in (1051 / 1250 : ℝ)..1, gC (11 / 20 : ℝ) 0 v ≤ (35370061 / 100000000 : ℝ) := by
  have h := (fsplit_up (11 / 20 : ℝ) (by norm_num) (by norm_num) (1051 / 1250 : ℝ) (8607 / 10000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fpiece_up (11 / 20 : ℝ) (1051 / 1250 : ℝ) (8607 / 10000 : ℝ) (23753 / 10000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold yC; norm_num)) (fsplit_up (11 / 20 : ℝ) (by norm_num) (by norm_num) (8607 / 10000 : ℝ) (4403 / 5000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fpiece_up (11 / 20 : ℝ) (8607 / 10000 : ℝ) (4403 / 5000 : ℝ) (11681 / 5000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold yC; norm_num)) (fsplit_up (11 / 20 : ℝ) (by norm_num) (by norm_num) (4403 / 5000 : ℝ) (1801 / 2000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fpiece_up (11 / 20 : ℝ) (4403 / 5000 : ℝ) (1801 / 2000 : ℝ) (4589 / 2000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold yC; norm_num)) (fsplit_up (11 / 20 : ℝ) (by norm_num) (by norm_num) (1801 / 2000 : ℝ) (2301 / 2500 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fpiece_up (11 / 20 : ℝ) (1801 / 2000 : ℝ) (2301 / 2500 : ℝ) (22503 / 10000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold yC; norm_num)) (fsplit_up (11 / 20 : ℝ) (by norm_num) (by norm_num) (2301 / 2500 : ℝ) (9403 / 10000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fpiece_up (11 / 20 : ℝ) (2301 / 2500 : ℝ) (9403 / 10000 : ℝ) (22039 / 10000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold yC; norm_num)) (fsplit_up (11 / 20 : ℝ) (by norm_num) (by norm_num) (9403 / 10000 : ℝ) (4801 / 5000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fpiece_up (11 / 20 : ℝ) (9403 / 10000 : ℝ) (4801 / 5000 : ℝ) (10777 / 5000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold yC; norm_num)) (fsplit_up (11 / 20 : ℝ) (by norm_num) (by norm_num) (4801 / 5000 : ℝ) (9801 / 10000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fpiece_up (11 / 20 : ℝ) (4801 / 5000 : ℝ) (9801 / 10000 : ℝ) (21051 / 10000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold yC; norm_num)) (fpiece_up (11 / 20 : ℝ) (9801 / 10000 : ℝ) (1 : ℝ) (5133 / 2500 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold yC; norm_num)))))))))
  norm_num at h ⊢; linarith

theorem fJ3_lo : (95870309 / 100000000 : ℝ) ≤ ∫ v in (5947 / 10000 : ℝ)..1, gC (11 / 20 : ℝ) 0 v := by
  have h := (fsplit_lo (11 / 20 : ℝ) (by norm_num) (by norm_num) (5947 / 10000 : ℝ) (3227 / 5000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fpiece_lo (11 / 20 : ℝ) (5947 / 10000 : ℝ) (3227 / 5000 : ℝ) (6551 / 2500 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold yC; norm_num)) (fsplit_lo (11 / 20 : ℝ) (by norm_num) (by norm_num) (3227 / 5000 : ℝ) (6961 / 10000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fpiece_lo (11 / 20 : ℝ) (3227 / 5000 : ℝ) (6961 / 10000 : ℝ) (12897 / 5000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold yC; norm_num)) (fsplit_lo (11 / 20 : ℝ) (by norm_num) (by norm_num) (6961 / 10000 : ℝ) (7467 / 10000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fpiece_lo (11 / 20 : ℝ) (6961 / 10000 : ℝ) (7467 / 10000 : ℝ) (25237 / 10000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold yC; norm_num)) (fsplit_lo (11 / 20 : ℝ) (by norm_num) (by norm_num) (7467 / 10000 : ℝ) (3987 / 5000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fpiece_lo (11 / 20 : ℝ) (7467 / 10000 : ℝ) (3987 / 5000 : ℝ) (1532 / 625 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold yC; norm_num)) (fsplit_lo (11 / 20 : ℝ) (by norm_num) (by norm_num) (3987 / 5000 : ℝ) (8481 / 10000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fpiece_lo (11 / 20 : ℝ) (3987 / 5000 : ℝ) (8481 / 10000 : ℝ) (5903 / 2500 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold yC; norm_num)) (fsplit_lo (11 / 20 : ℝ) (by norm_num) (by norm_num) (8481 / 10000 : ℝ) (8987 / 10000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fpiece_lo (11 / 20 : ℝ) (8481 / 10000 : ℝ) (8987 / 10000 : ℝ) (22543 / 10000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold yC; norm_num)) (fsplit_lo (11 / 20 : ℝ) (by norm_num) (by norm_num) (8987 / 10000 : ℝ) (4747 / 5000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fpiece_lo (11 / 20 : ℝ) (8987 / 10000 : ℝ) (4747 / 5000 : ℝ) (853 / 400 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold yC; norm_num)) (fpiece_lo (11 / 20 : ℝ) (4747 / 5000 : ℝ) (1 : ℝ) (2 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold yC; norm_num)))))))))
  norm_num at h ⊢; linarith

theorem fJ3_up : ∫ v in (2973 / 5000 : ℝ)..1, gC (11 / 20 : ℝ) 0 v ≤ (99190067 / 100000000 : ℝ) := by
  have h := (fsplit_up (11 / 20 : ℝ) (by norm_num) (by norm_num) (2973 / 5000 : ℝ) (6453 / 10000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fpiece_up (11 / 20 : ℝ) (2973 / 5000 : ℝ) (6453 / 10000 : ℝ) (13247 / 5000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold yC; norm_num)) (fsplit_up (11 / 20 : ℝ) (by norm_num) (by norm_num) (6453 / 10000 : ℝ) (87 / 125 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fpiece_up (11 / 20 : ℝ) (6453 / 10000 : ℝ) (87 / 125 : ℝ) (13103 / 5000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold yC; norm_num)) (fsplit_up (11 / 20 : ℝ) (by norm_num) (by norm_num) (87 / 125 : ℝ) (7467 / 10000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fpiece_up (11 / 20 : ℝ) (87 / 125 : ℝ) (7467 / 10000 : ℝ) (6449 / 2500 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold yC; norm_num)) (fsplit_up (11 / 20 : ℝ) (by norm_num) (by norm_num) (7467 / 10000 : ℝ) (7973 / 10000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fpiece_up (11 / 20 : ℝ) (7467 / 10000 : ℝ) (7973 / 10000 : ℝ) (12619 / 5000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold yC; norm_num)) (fsplit_up (11 / 20 : ℝ) (by norm_num) (by norm_num) (7973 / 10000 : ℝ) (106 / 125 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fpiece_up (11 / 20 : ℝ) (7973 / 10000 : ℝ) (106 / 125 : ℝ) (4903 / 2000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold yC; norm_num)) (fsplit_up (11 / 20 : ℝ) (by norm_num) (by norm_num) (106 / 125 : ℝ) (8987 / 10000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fpiece_up (11 / 20 : ℝ) (106 / 125 : ℝ) (8987 / 10000 : ℝ) (11807 / 5000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold yC; norm_num)) (fsplit_up (11 / 20 : ℝ) (by norm_num) (by norm_num) (8987 / 10000 : ℝ) (4747 / 5000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fpiece_up (11 / 20 : ℝ) (8987 / 10000 : ℝ) (4747 / 5000 : ℝ) (1409 / 625 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold yC; norm_num)) (fpiece_up (11 / 20 : ℝ) (4747 / 5000 : ℝ) (1 : ℝ) (10663 / 5000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold yC; norm_num)))))))))
  norm_num at h ⊢; linarith

open Checked.Trust.NCAQ Checked.Trust.NCAR in
theorem Bh12_1 : (234437 / 1000000 : ℝ) ≤ Bc (346 / 100 : ℝ) (163 / 100 : ℝ) (1 / 2 * (Real.log 2 / Real.log 10)) ∧
    Bc (346 / 100 : ℝ) (163 / 100 : ℝ) (1 / 2 * (Real.log 2 / Real.log 10)) ≤ (234481 / 1000000 : ℝ) := by
  obtain ⟨l1, l2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10
  have q2 := pow_le_pow_left₀ (by norm_num) l1 2
  have q2' := pow_le_pow_left₀ (by linarith) l2 2
  have q3 := pow_le_pow_left₀ (by norm_num) l1 3
  have q3' := pow_le_pow_left₀ (by linarith) l2 3
  unfold Bc; constructor <;> (ring_nf; ring_nf at q2 q2' q3 q3'; linarith)

open Checked.Trust.NCAQ Checked.Trust.NCAR in
theorem Bh12_3 : (1306929 / 1000000 : ℝ) ≤ Bc (346 / 100 : ℝ) (163 / 100 : ℝ) (3 / 2 * (Real.log 2 / Real.log 10)) ∧
    Bc (346 / 100 : ℝ) (163 / 100 : ℝ) (3 / 2 * (Real.log 2 / Real.log 10)) ≤ (1307237 / 1000000 : ℝ) := by
  obtain ⟨l1, l2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10
  have q2 := pow_le_pow_left₀ (by norm_num) l1 2
  have q2' := pow_le_pow_left₀ (by linarith) l2 2
  have q3 := pow_le_pow_left₀ (by norm_num) l1 3
  have q3' := pow_le_pow_left₀ (by linarith) l2 3
  unfold Bc; constructor <;> (ring_nf; ring_nf at q2 q2' q3 q3'; linarith)

/-- In the generic model, the source placed at `v = √(1/r)` has redshift `r − 1`. -/
theorem ma_redshift {m k c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hy : ∀ v ∈ Icc c 1, 0 < yC m k v)
    {r : ℝ} (hr : 0 < r) :
    redshift (ma m k c hc hc1 hy) (mtau m k c 1) (mtau m k c √(1 / r)) = r - 1 := by
  unfold redshift; rw [ma_tau, ma_tau, Real.sq_sqrt (by positivity)]; field_simp

open Checked.Trust.NCAQ Checked.Trust.NCAR Checked.Cosmography.B1 in
/-- `rl19_box_unmatched` without the redshift of the farthest source: the flat model of matter density
eleven twentieths, the farthest source placed at the middle one; the box cubic `a₂ = 3.46`, `a₃ = 1.63`
(normalisation `H = 1.0879`) matches the remaining two distance moduli within 1/20 mag of zero. -/
theorem rl19_box_unmatched_h12 : necessity% Checked.Cosmography.B1FitRL19.rl19_box_unmatched 12 := by
  obtain ⟨s1, s2⟩ := sqrt2_bd
  obtain ⟨l1, l2⟩ := log10_bd
  obtain ⟨v1a, v1b⟩ := v1_bd
  obtain ⟨v3a, v3b⟩ := v3_bd
  set c := √(1 / (2 * √2)) with hcdef
  set w1 := √(1 / √2) with hw1def
  have hc : 0 < c := by linarith
  have hc1 : c ≤ 1 := by linarith
  have hy : ∀ v ∈ Icc c 1, 0 < yC (11 / 20) 0 v := fun v _ => fy_pos (by norm_num) (by norm_num) v
  have hw1m : w1 ∈ Icc c 1 := ⟨by linarith, by linarith⟩
  have hcm : c ∈ Icc c 1 := ⟨le_rfl, hc1⟩
  set a := ma (11 / 20) 0 c hc hc1 hy with hadef
  have hmono := (mtau_strictMono hc hc1 hy).monotone
  set T := mtau (11 / 20) 0 c with hTdef
  have ha0 : a (T 1) = 1 := by rw [hadef, ma_tau]; norm_num
  have hH0 : hubble a (T 1) = 1 := ma_hubble0 hc hc1 hy
  have hz1 : redshift a (T 1) (T w1) = √2 - 1 := ma_redshift hc hc1 hy (by positivity)
  have hz3 : redshift a (T 1) (T c) = 2 * √2 - 1 := ma_redshift hc hc1 hy (by positivity)
  have hχ1 : comoving a (T 1) (T w1) = ∫ v in w1..1, gC (11 / 20) 0 v := ma_comoving hc hc1 hy hw1m
  have hχ3 : comoving a (T 1) (T c) = ∫ v in c..1, gC (11 / 20) 0 v := ma_comoving hc hc1 hy hcm
  have hd1 : lumDistFlat a (T 1) (T w1) = √2 * ∫ v in w1..1, gC (11 / 20) 0 v := by
    unfold lumDistFlat; rw [ha0, hz1, hχ1]; ring
  have hd3 : lumDistFlat a (T 1) (T c) = 2 * √2 * ∫ v in c..1, gC (11 / 20) 0 v := by
    unfold lumDistFlat; rw [ha0, hz3, hχ3]; ring
  have J1l : (17299219 / 50000000 : ℝ) ≤ ∫ v in w1..1, gC (11 / 20) 0 v :=
    le_trans fJ1_lo (fshift _ (by norm_num) (by norm_num) (by linarith))
  have J1u : ∫ v in w1..1, gC (11 / 20) 0 v ≤ (35370061 / 100000000 : ℝ) :=
    le_trans (fshift _ (by norm_num) (by norm_num) (by linarith)) fJ1_up
  have J3l : (95870309 / 100000000 : ℝ) ≤ ∫ v in c..1, gC (11 / 20) 0 v :=
    le_trans fJ3_lo (fshift _ (by norm_num) (by norm_num) (by linarith))
  have J3u : ∫ v in c..1, gC (11 / 20) 0 v ≤ (99190067 / 100000000 : ℝ) :=
    le_trans (fshift _ (by norm_num) (by norm_num) (by linarith)) fJ3_up
  have D1l : 1.41421 * (17299219 / 50000000 : ℝ) ≤ lumDistFlat a (T 1) (T w1) := by
    rw [hd1]; exact mul_le_mul s1 J1l (by norm_num) (by linarith)
  have D1u : lumDistFlat a (T 1) (T w1) ≤ 1.41422 * (35370061 / 100000000 : ℝ) := by
    rw [hd1]; exact mul_le_mul s2 J1u (by linarith) (by norm_num)
  have D3l : 2 * 1.41421 * (95870309 / 100000000 : ℝ) ≤ lumDistFlat a (T 1) (T c) := by
    rw [hd3]; exact mul_le_mul (by linarith) J3l (by norm_num) (by linarith)
  have D3u : lumDistFlat a (T 1) (T c) ≤ 2 * 1.41422 * (99190067 / 100000000 : ℝ) := by
    rw [hd3]; exact mul_le_mul (by linarith) J3u (by linarith) (by norm_num)
  have P1 : logPolyDL3 (346 / 100 : ℝ) (163 / 100 : ℝ) (10879 / 10000 : ℝ) (redshift a (T 1) (T w1))
      = Real.log 10 / (10879 / 10000 : ℝ) * Bc (346 / 100 : ℝ) (163 / 100 : ℝ)
        (1 / 2 * (Real.log 2 / Real.log 10)) := by
    rw [hz1, poly3_eq _ _ _ (1 / 2) _ log_s2]
  have P3 : logPolyDL3 (346 / 100 : ℝ) (163 / 100 : ℝ) (10879 / 10000 : ℝ) (redshift a (T 1) (T c))
      = Real.log 10 / (10879 / 10000 : ℝ) * Bc (346 / 100 : ℝ) (163 / 100 : ℝ)
        (3 / 2 * (Real.log 2 / Real.log 10)) := by
    rw [hz3, poly3_eq _ _ _ (3 / 2) _ log_2s2]
  have pp1 : 0 < logPolyDL3 (346 / 100 : ℝ) (163 / 100 : ℝ) (10879 / 10000 : ℝ) (redshift a (T 1) (T w1)) := by
    rw [P1]; exact pos_of _ _ _ _ _ (by norm_num) l1 Bh12_1.1 (by norm_num) (by norm_num)
  have pp3 : 0 < logPolyDL3 (346 / 100 : ℝ) (163 / 100 : ℝ) (10879 / 10000 : ℝ) (redshift a (T 1) (T c)) := by
    rw [P3]; exact pos_of _ _ _ _ _ (by norm_num) l1 Bh12_3.1 (by norm_num) (by norm_num)
  have m1 : |5 * Real.logb 10 (lumDistFlat a (T 1) (T w1) / logPolyDL3 (346 / 100 : ℝ) (163 / 100 : ℝ)
      (10879 / 10000 : ℝ) (redshift a (T 1) (T w1))) - 0| ≤ 1 / 20 := by
    rw [P1]
    exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 Bh12_1.1 Bh12_1.2 D1l D1u
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have m3 : |5 * Real.logb 10 (lumDistFlat a (T 1) (T c) / logPolyDL3 (346 / 100 : ℝ) (163 / 100 : ℝ)
      (10879 / 10000 : ℝ) (redshift a (T 1) (T c))) - 0| ≤ 1 / 20 := by
    rw [P3]
    exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 Bh12_3.1 Bh12_3.2 D3l D3u
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hcw : c ≤ w1 := hw1m.1
  refine ⟨11 / 20, by norm_num, by norm_num, a, T c, T c, T w1, T 1, le_rfl, hmono hcw, hmono hw1m.2,
    fun s hs => ma_pos hc hc1 hy hs, fun s _ => (ma_deriv hc hc1 hy s).differentiableAt,
    by rw [hH0]; norm_num, ?_, hz1, hz3, (346 / 100 : ℝ), (163 / 100 : ℝ), (10879 / 10000 : ℝ), 0,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, pp1, pp3, pp3, ?_⟩
  · intro s hs
    rw [ma_law hc hc1 hy hs]
    congr 2; ring
  · exact ⟨m1, m3, m3⟩

/-! ## The law hypothesis of the two-redshift B1 headlines: Einstein–de Sitter distances -/

/-- A residual distance modulus within 1/20 mag of zero from hundredth powers of interval ends. -/
theorem resid_band100 (L B d H Ll Lu Bl Bu dl du yl yu : ℝ) (hH : 0 < H) (hL : Ll ≤ L) (hL' : L ≤ Lu)
    (hB : Bl ≤ B) (hB' : B ≤ Bu) (hd : dl ≤ d) (hd' : d ≤ du) (hLl : 0 < Ll) (hBl : 0 < Bl)
    (hyl : 0 < yl) (c1 : yl ≤ dl / (Lu / H * Bu)) (c2 : du / (Ll / H * Bl) ≤ yu)
    (p1 : 1 ≤ 10 * yl ^ 100) (p2 : yu ^ 100 ≤ 10) :
    |5 * Real.logb 10 (d / (L / H * B)) - 0| ≤ 1 / 20 := by
  have hPl : Ll / H * Bl ≤ L / H * B :=
    mul_le_mul (div_le_div_of_nonneg_right hL hH.le) hB hBl.le (div_nonneg (by linarith) hH.le)
  have hPu : L / H * B ≤ Lu / H * Bu :=
    mul_le_mul (div_le_div_of_nonneg_right hL' hH.le) hB' (by linarith) (div_nonneg (by linarith) hH.le)
  have hP0 : 0 < Ll / H * Bl := by positivity
  have hP : 0 < L / H * B := by linarith
  have hdl : 0 < dl := by
    by_contra hneg; push Not at hneg
    have : dl / (Lu / H * Bu) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hneg (by linarith)
    linarith
  set y := d / (L / H * B) with hy
  have hyl' : yl ≤ y := by
    refine le_trans c1 ?_
    rw [hy]; exact div_le_div₀ (by linarith) hd hP hPu
  have hyu' : y ≤ yu := by
    refine le_trans ?_ c2
    rw [hy]; exact div_le_div₀ (by linarith) hd' hP0 hPl
  have hy0 : 0 < y := lt_of_lt_of_le hyl hyl'
  have hl10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have up : 100 * Real.log y ≤ Real.log 10 := by
    have h1 : y ^ 100 ≤ 10 := le_trans (pow_le_pow_left₀ hy0.le hyu' 100) p2
    have := Real.log_le_log (by positivity) h1
    rwa [Real.log_pow] at this
  have lo : 0 ≤ Real.log 10 + 100 * Real.log y := by
    have h1 : 1 ≤ 10 * y ^ 100 := le_trans p1
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hyl.le hyl' 100) (by norm_num))
    have := Real.log_le_log (by norm_num) h1
    rwa [Real.log_one, Real.log_mul (by norm_num) (by positivity), Real.log_pow] at this
  rw [sub_zero, abs_le, Real.logb]
  constructor
  · rw [show 5 * (Real.log y / Real.log 10) = (5 * Real.log y) / Real.log 10 by ring,
      le_div_iff₀ hl10]
    push_cast at lo; linarith
  · rw [show 5 * (Real.log y / Real.log 10) = (5 * Real.log y) / Real.log 10 by ring,
      div_le_iff₀ hl10]
    push_cast at up; linarith

theorem s8_bd : (353553 / 1000000 : ℝ) ≤ √(1 / 8) ∧ √(1 / 8) ≤ (353554 / 1000000 : ℝ) := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · rw [show (353554 / 1000000 : ℝ) = √((353554 / 1000000) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)

theorem log_4 : Real.log (1 + 3) = 2 * Real.log 2 := by
  rw [show (1:ℝ) + 3 = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring

theorem log_8 : Real.log (1 + 7) = 3 * Real.log 2 := by
  rw [show (1:ℝ) + 7 = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring

open Checked.Trust.NCAQ Checked.Trust.NCAR in
/-- Einstein–de Sitter at `z = 3` and `z = 7`: ordered source times, the model hypotheses, the redshifts and
the distances `6` and `24(1 − √(1/8))` (`H₀ = 2/3`). -/
theorem ea37 : tE 8 ≤ tE 4 ∧ tE 4 ≤ 1 ∧ 0 < tE 8 ∧ redshift ea 1 (tE 4) = 3 ∧ redshift ea 1 (tE 8) = 7 ∧
    lumDistFlat ea 1 (tE 4) = 6 ∧ lumDistFlat ea 1 (tE 8) = 24 * (1 - √(1 / 8)) := by
  obtain ⟨-, h41, h4z, -⟩ := tE_props 4 (by norm_num)
  obtain ⟨h80, -, h8z, -⟩ := tE_props 8 (by norm_num)
  refine ⟨tE_anti _ _ (by norm_num) (by norm_num), h41, h80, by rw [h4z]; norm_num, by rw [h8z]; norm_num,
    ?_, ?_⟩
  · rw [ea_dL 4 (by norm_num), show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num
  · rw [ea_dL 8 (by norm_num)]; ring

open Checked.Trust.NCAQ Checked.Trust.NCAR in
theorem Bsep3 : (2832003 / 1000000 : ℝ) ≤ Bc (3203 / 1000 : ℝ) (49 / 10 : ℝ) (2 * (Real.log 2 / Real.log 10)) ∧
    Bc (3203 / 1000 : ℝ) (49 / 10 : ℝ) (2 * (Real.log 2 / Real.log 10)) ≤ (1416409 / 500000 : ℝ) := by
  obtain ⟨l1, l2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10
  have q2 := pow_le_pow_left₀ (by norm_num) l1 2
  have q2' := pow_le_pow_left₀ (by linarith) l2 2
  have q3 := pow_le_pow_left₀ (by norm_num) l1 3
  have q3' := pow_le_pow_left₀ (by linarith) l2 3
  unfold Bc; constructor <;> (ring_nf; ring_nf at q2 q2' q3 q3'; linarith)

open Checked.Trust.NCAQ Checked.Trust.NCAR in
theorem Bsep7 : (3561629 / 500000 : ℝ) ≤ Bc (3203 / 1000 : ℝ) (49 / 10 : ℝ) (3 * (Real.log 2 / Real.log 10)) ∧
    Bc (3203 / 1000 : ℝ) (49 / 10 : ℝ) (3 * (Real.log 2 / Real.log 10)) ≤ (890689 / 125000 : ℝ) := by
  obtain ⟨l1, l2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10
  have q2 := pow_le_pow_left₀ (by norm_num) l1 2
  have q2' := pow_le_pow_left₀ (by linarith) l2 2
  have q3 := pow_le_pow_left₀ (by norm_num) l1 3
  have q3' := pow_le_pow_left₀ (by linarith) l2 3
  unfold Bc; constructor <;> (ring_nf; ring_nf at q2 q2' q3 q3'; linarith)

open Checked.Trust.NCAQ Checked.Trust.NCAR in
theorem Bdir3 : (82297 / 800 : ℝ) ≤ Bc (27747 / 125 : ℝ) (100 : ℝ) (2 * (Real.log 2 / Real.log 10)) ∧
    Bc (27747 / 125 : ℝ) (100 : ℝ) (2 * (Real.log 2 / Real.log 10)) ≤ (51450707 / 500000 : ℝ) := by
  obtain ⟨l1, l2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10
  have q2 := pow_le_pow_left₀ (by norm_num) l1 2
  have q2' := pow_le_pow_left₀ (by linarith) l2 2
  have q3 := pow_le_pow_left₀ (by norm_num) l1 3
  have q3' := pow_le_pow_left₀ (by linarith) l2 3
  unfold Bc; constructor <;> (ring_nf; ring_nf at q2 q2' q3 q3'; linarith)

open Checked.Trust.NCAQ Checked.Trust.NCAR in
theorem Bdir7 : (15972191 / 62500 : ℝ) ≤ Bc (27747 / 125 : ℝ) (100 : ℝ) (3 * (Real.log 2 / Real.log 10)) ∧
    Bc (27747 / 125 : ℝ) (100 : ℝ) (3 * (Real.log 2 / Real.log 10)) ≤ (255632649 / 1000000 : ℝ) := by
  obtain ⟨l1, l2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10
  have q2 := pow_le_pow_left₀ (by norm_num) l1 2
  have q2' := pow_le_pow_left₀ (by linarith) l2 2
  have q3 := pow_le_pow_left₀ (by norm_num) l1 3
  have q3' := pow_le_pow_left₀ (by linarith) l2 3
  unfold Bc; constructor <;> (ring_nf; ring_nf at q2 q2' q3 q3'; linarith)

open Checked.Trust.NCAQ Checked.Trust.NCAR Checked.Cosmography.B1 in
/-- `cubic_separation` without the expansion law: the Einstein–de Sitter universe (density one) observed with
the density parameter one fifth; the cubic `a₂ = 3.203`, `a₃ = 4.9` (normalisation `H = 1.0721`) matches both
distance moduli within 1/20 mag of zero and lies within `5/4` of the ΛCDM-implied point. -/
theorem cubic_separation_h8 : necessity% Checked.Cosmography.B1Sep.cubic_separation 8 := by
  obtain ⟨o84, o41, p8, hz3, hz7, hd3, hd7⟩ := ea37
  obtain ⟨l1, l2⟩ := log10_bd
  obtain ⟨e1, e2⟩ := s8_bd
  obtain ⟨hp, hd, hH₀, -⟩ := ea_hyps _ p8
  have P3 : logPolyDL3 (3203 / 1000 : ℝ) (49 / 10 : ℝ) (10721 / 10000 : ℝ) (redshift ea 1 (tE 4))
      = Real.log 10 / (10721 / 10000 : ℝ) * Bc (3203 / 1000 : ℝ) (49 / 10 : ℝ) (2 * (Real.log 2 / Real.log 10)) := by
    rw [hz3, poly3_eq _ _ _ 2 _ log_4]
  have P7 : logPolyDL3 (3203 / 1000 : ℝ) (49 / 10 : ℝ) (10721 / 10000 : ℝ) (redshift ea 1 (tE 8))
      = Real.log 10 / (10721 / 10000 : ℝ) * Bc (3203 / 1000 : ℝ) (49 / 10 : ℝ) (3 * (Real.log 2 / Real.log 10)) := by
    rw [hz7, poly3_eq _ _ _ 3 _ log_8]
  refine ⟨1 / 5, by norm_num, by norm_num, ea, tE 8, tE 4, 1, o84, o41, hp, hd, hH₀, hz3, hz7,
    (3203 / 1000 : ℝ), (49 / 10 : ℝ), (10721 / 10000 : ℝ), 0, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · rw [P3]; exact pos_of _ _ _ _ _ (by norm_num) l1 Bsep3.1 (by norm_num) (by norm_num)
  · rw [P7]; exact pos_of _ _ _ _ _ (by norm_num) l1 Bsep7.1 (by norm_num) (by norm_num)
  · rw [P3, hd3]
    exact resid_band100 _ _ _ _ _ _ _ _ 6 6 (98613 / 100000) (15414 / 15625) (by norm_num) l1 l2
      Bsep3.1 Bsep3.2 le_rfl le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · rw [P7, hd7]
    exact resid_band100 _ _ _ _ _ _ _ _ (24 * (1 - 353554 / 1000000)) (24 * (1 - 353553 / 1000000))
      (202749 / 200000) (126769 / 125000) (by norm_num) l1 l2 Bsep7.1 Bsep7.2 (by linarith) (by linarith)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [not_lt]
    unfold lusA2 lusA3
    have hA2l : 2.30249 * (3 / 2 - 3 / 4 * (1 / 5)) ≤ Real.log 10 * (3 / 2 - 3 / 4 * (1 / 5 : ℝ)) := by nlinarith
    have hA2u : Real.log 10 * (3 / 2 - 3 / 4 * (1 / 5 : ℝ)) ≤ 2.30268 * (3 / 2 - 3 / 4 * (1 / 5)) := by nlinarith
    have hsq1 : (2.30249 : ℝ) ^ 2 ≤ Real.log 10 ^ 2 := pow_le_pow_left₀ (by norm_num) l1 2
    have hsq2 : Real.log 10 ^ 2 ≤ (2.30268 : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) l2 2
    have hc : (0:ℝ) ≤ 9 / 8 * (1 / 5) ^ 2 - 2 * (1 / 5) + 7 / 6 := by norm_num
    have hA3l := mul_le_mul_of_nonneg_right hsq1 hc
    have hA3u := mul_le_mul_of_nonneg_right hsq2 hc
    set A2 := Real.log 10 * (3 / 2 - 3 / 4 * (1 / 5 : ℝ))
    set A3 := Real.log 10 ^ 2 * (9 / 8 * (1 / 5 : ℝ) ^ 2 - 2 * (1 / 5) + 7 / 6)
    norm_num at hA2l hA2u hA3l hA3u ⊢
    nlinarith

open Checked.Trust.NCAQ Checked.Trust.NCAR Checked.Cosmography.B1 in
/-- `cubic_direction` without the expansion law: the Einstein–de Sitter universe observed with the density
parameter one fifth; the cubic `a₂ = 27747/125`, `a₃ = 100` (normalisation `H = 38.701`) matches both distance
moduli within 1/20 mag of zero and lies on the other side of the line. -/
theorem cubic_direction_h8 : necessity% Checked.Cosmography.B1Sep.cubic_direction 8 := by
  obtain ⟨o84, o41, p8, hz3, hz7, hd3, hd7⟩ := ea37
  obtain ⟨l1, l2⟩ := log10_bd
  obtain ⟨m1, m2⟩ := lam_bd
  obtain ⟨e1, e2⟩ := s8_bd
  obtain ⟨hp, hd, hH₀, -⟩ := ea_hyps _ p8
  have P3 : logPolyDL3 (27747 / 125 : ℝ) (100 : ℝ) (38701 / 1000 : ℝ) (redshift ea 1 (tE 4))
      = Real.log 10 / (38701 / 1000 : ℝ) * Bc (27747 / 125 : ℝ) (100 : ℝ) (2 * (Real.log 2 / Real.log 10)) := by
    rw [hz3, poly3_eq _ _ _ 2 _ log_4]
  have P7 : logPolyDL3 (27747 / 125 : ℝ) (100 : ℝ) (38701 / 1000 : ℝ) (redshift ea 1 (tE 8))
      = Real.log 10 / (38701 / 1000 : ℝ) * Bc (27747 / 125 : ℝ) (100 : ℝ) (3 * (Real.log 2 / Real.log 10)) := by
    rw [hz7, poly3_eq _ _ _ 3 _ log_8]
  refine ⟨1 / 5, by norm_num, by norm_num, ea, tE 8, tE 4, 1, o84, o41, hp, hd, hH₀, hz3, hz7,
    (27747 / 125 : ℝ), (100 : ℝ), (38701 / 1000 : ℝ), 0, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · rw [P3]; exact pos_of _ _ _ _ _ (by norm_num) l1 Bdir3.1 (by norm_num) (by norm_num)
  · rw [P7]; exact pos_of _ _ _ _ _ (by norm_num) l1 Bdir7.1 (by norm_num) (by norm_num)
  · rw [P3, hd3]
    exact resid_band100 _ _ _ _ _ _ _ _ 6 6 (489991 / 500000) (15318 / 15625) (by norm_num) l1 l2
      Bdir3.1 Bdir3.2 le_rfl le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · rw [P7, hd7]
    exact resid_band100 _ _ _ _ _ _ _ _ (24 * (1 - 353554 / 1000000)) (24 * (1 - 353553 / 1000000))
      (255009 / 250000) (1020433 / 1000000) (by norm_num) l1 l2 Bdir7.1 Bdir7.2 (by linarith) (by linarith)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [not_lt]
    unfold lusA2 lusA3
    have hlb : Real.logb 10 2 = Real.log 2 / Real.log 10 := rfl
    rw [hlb]
    have hsq2 : Real.log 10 ^ 2 ≤ (2.30268 : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) l2 2
    have hsq1 : (2.30249 : ℝ) ^ 2 ≤ Real.log 10 ^ 2 := pow_le_pow_left₀ (by norm_num) l1 2
    set lam := Real.log 2 / Real.log 10
    set A3 := Real.log 10 ^ 2 * (9 / 8 * (1 / 5 : ℝ) ^ 2 - 2 * (1 / 5) + 7 / 6) with hA3
    have hA3l : 0 ≤ A3 := by rw [hA3]; positivity
    have hA3u : A3 ≤ (2.30268 : ℝ) ^ 2 * (9 / 8 * (1 / 5 : ℝ) ^ 2 - 2 * (1 / 5) + 7 / 6) :=
      mul_le_mul_of_nonneg_right hsq2 (by norm_num)
    have hk : 7 * lam * (100 - A3) ≤ 7 * 0.30105 * 100 := by
      have : 0 ≤ 7 * lam := by linarith
      nlinarith
    nlinarith

/-! ## `fit_direction` without `Ω ≤ 1`: the flat model of negative cosmological constant at three halves -/

open Checked.Trust.NCAQ in
theorem gsplit_lo (Ω : ℝ) (hΩ : 1 ≤ Ω) (p q r : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hqr : q ≤ r) (hr : r ≤ 1)
    {A B : ℝ} (h1 : A ≤ ∫ v in p..q, 2 / √(Ω + (1 - Ω) * v ^ 6))
    (h2 : B ≤ ∫ v in q..r, 2 / √(Ω + (1 - Ω) * v ^ 6)) :
    A + B ≤ ∫ v in p..r, 2 / √(Ω + (1 - Ω) * v ^ 6) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((g_cont Ω p q hΩ hp (le_trans hqr hr)).intervalIntegrable_of_Icc hpq)
    ((g_cont Ω q r hΩ (le_trans hp hpq) hr).intervalIntegrable_of_Icc hqr)]
  linarith

open Checked.Trust.NCAQ in
theorem gsplit_up (Ω : ℝ) (hΩ : 1 ≤ Ω) (p q r : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hqr : q ≤ r) (hr : r ≤ 1)
    {A B : ℝ} (h1 : ∫ v in p..q, 2 / √(Ω + (1 - Ω) * v ^ 6) ≤ A)
    (h2 : ∫ v in q..r, 2 / √(Ω + (1 - Ω) * v ^ 6) ≤ B) :
    ∫ v in p..r, 2 / √(Ω + (1 - Ω) * v ^ 6) ≤ A + B := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((g_cont Ω p q hΩ hp (le_trans hqr hr)).intervalIntegrable_of_Icc hpq)
    ((g_cont Ω q r hΩ (le_trans hp hpq) hr).intervalIntegrable_of_Icc hqr)]
  linarith

open Checked.Trust.NCAQ in
/-- Moving the lower end of `∫_w^1 2/√(Ω + (1 − Ω)v⁶)` up decreases it. -/
theorem gshift (Ω : ℝ) (hΩ : 1 ≤ Ω) {w w' : ℝ} (hw : 0 ≤ w) (hww : w ≤ w') (hw' : w' ≤ 1) :
    ∫ v in w'..1, 2 / √(Ω + (1 - Ω) * v ^ 6) ≤ ∫ v in w..1, 2 / √(Ω + (1 - Ω) * v ^ 6) := by
  rw [int_split Ω w w' hΩ hw hww hw']
  have : 0 ≤ ∫ v in w..w', 2 / √(Ω + (1 - Ω) * v ^ 6) :=
    intervalIntegral.integral_nonneg hww (fun v _ => div_nonneg (by norm_num) (Real.sqrt_nonneg _))
  linarith

open Checked.Trust.NCAR in
theorem gJ1_lo : (3626869 / 12500000 : ℝ) ≤ ∫ v in (8409 / 10000 : ℝ)..1, 2 / √((3 / 2 : ℝ) + (1 - (3 / 2 : ℝ)) * v ^ 6) := by
  have h := (gsplit_lo (3 / 2 : ℝ) (by norm_num) (8409 / 10000 : ℝ) (4391 / 5000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_lo (3 / 2 : ℝ) (8409 / 10000 : ℝ) (4391 / 5000 : ℝ) (8693 / 5000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (gsplit_lo (3 / 2 : ℝ) (by norm_num) (4391 / 5000 : ℝ) (4553 / 5000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_lo (3 / 2 : ℝ) (4391 / 5000 : ℝ) (4553 / 5000 : ℝ) (8871 / 5000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (gsplit_lo (3 / 2 : ℝ) (by norm_num) (4553 / 5000 : ℝ) (9379 / 10000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_lo (3 / 2 : ℝ) (4553 / 5000 : ℝ) (9379 / 10000 : ℝ) (1134 / 625 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (gsplit_lo (3 / 2 : ℝ) (by norm_num) (9379 / 10000 : ℝ) (9603 / 10000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_lo (3 / 2 : ℝ) (9379 / 10000 : ℝ) (9603 / 10000 : ℝ) (4643 / 2500 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (gsplit_lo (3 / 2 : ℝ) (by norm_num) (9603 / 10000 : ℝ) (9777 / 10000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_lo (3 / 2 : ℝ) (9603 / 10000 : ℝ) (9777 / 10000 : ℝ) (19001 / 10000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (gsplit_lo (3 / 2 : ℝ) (by norm_num) (9777 / 10000 : ℝ) (9901 / 10000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_lo (3 / 2 : ℝ) (9777 / 10000 : ℝ) (9901 / 10000 : ℝ) (3879 / 2000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (gsplit_lo (3 / 2 : ℝ) (by norm_num) (9901 / 10000 : ℝ) (1247 / 1250 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_lo (3 / 2 : ℝ) (9901 / 10000 : ℝ) (1247 / 1250 : ℝ) (4929 / 2500 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (piece_lo (3 / 2 : ℝ) (1247 / 1250 : ℝ) (1 : ℝ) (2491 / 1250 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)))))))))
  norm_num at h ⊢; linarith

open Checked.Trust.NCAR in
theorem gJ1_up : ∫ v in (1051 / 1250 : ℝ)..1, 2 / √((3 / 2 : ℝ) + (1 - (3 / 2 : ℝ)) * v ^ 6) ≤ (29636279 / 100000000 : ℝ) := by
  have h := (gsplit_up (3 / 2 : ℝ) (by norm_num) (1051 / 1250 : ℝ) (4391 / 5000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_up (3 / 2 : ℝ) (1051 / 1250 : ℝ) (4391 / 5000 : ℝ) (17743 / 10000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (gsplit_up (3 / 2 : ℝ) (by norm_num) (4391 / 5000 : ℝ) (1821 / 2000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_up (3 / 2 : ℝ) (4391 / 5000 : ℝ) (1821 / 2000 : ℝ) (1134 / 625 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (gsplit_up (3 / 2 : ℝ) (by norm_num) (1821 / 2000 : ℝ) (9379 / 10000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_up (3 / 2 : ℝ) (1821 / 2000 : ℝ) (9379 / 10000 : ℝ) (18573 / 10000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (gsplit_up (3 / 2 : ℝ) (by norm_num) (9379 / 10000 : ℝ) (4801 / 5000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_up (3 / 2 : ℝ) (9379 / 10000 : ℝ) (4801 / 5000 : ℝ) (19 / 10 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (gsplit_up (3 / 2 : ℝ) (by norm_num) (4801 / 5000 : ℝ) (9777 / 10000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_up (3 / 2 : ℝ) (4801 / 5000 : ℝ) (9777 / 10000 : ℝ) (4849 / 2500 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (gsplit_up (3 / 2 : ℝ) (by norm_num) (9777 / 10000 : ℝ) (9901 / 10000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_up (3 / 2 : ℝ) (9777 / 10000 : ℝ) (9901 / 10000 : ℝ) (19717 / 10000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (gsplit_up (3 / 2 : ℝ) (by norm_num) (9901 / 10000 : ℝ) (1247 / 1250 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_up (3 / 2 : ℝ) (9901 / 10000 : ℝ) (1247 / 1250 : ℝ) (19929 / 10000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (piece_up (3 / 2 : ℝ) (1247 / 1250 : ℝ) (1 : ℝ) (2 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)))))))))
  norm_num at h ⊢; linarith

open Checked.Trust.NCAR in
theorem gJ3_lo : (34919097 / 50000000 : ℝ) ≤ ∫ v in (5947 / 10000 : ℝ)..1, 2 / √((3 / 2 : ℝ) + (1 - (3 / 2 : ℝ)) * v ^ 6) := by
  have h := (gsplit_lo (3 / 2 : ℝ) (by norm_num) (5947 / 10000 : ℝ) (6897 / 10000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_lo (3 / 2 : ℝ) (5947 / 10000 : ℝ) (6897 / 10000 : ℝ) (16451 / 10000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (gsplit_lo (3 / 2 : ℝ) (by norm_num) (6897 / 10000 : ℝ) (7721 / 10000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_lo (3 / 2 : ℝ) (6897 / 10000 : ℝ) (7721 / 10000 : ℝ) (16631 / 10000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (gsplit_lo (3 / 2 : ℝ) (by norm_num) (7721 / 10000 : ℝ) (8417 / 10000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_lo (3 / 2 : ℝ) (7721 / 10000 : ℝ) (8417 / 10000 : ℝ) (8469 / 5000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (gsplit_lo (3 / 2 : ℝ) (by norm_num) (8417 / 10000 : ℝ) (8987 / 10000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_lo (3 / 2 : ℝ) (8417 / 10000 : ℝ) (8987 / 10000 : ℝ) (17393 / 10000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (gsplit_lo (3 / 2 : ℝ) (by norm_num) (8987 / 10000 : ℝ) (9431 / 10000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_lo (3 / 2 : ℝ) (8987 / 10000 : ℝ) (9431 / 10000 : ℝ) (3597 / 2000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (gsplit_lo (3 / 2 : ℝ) (by norm_num) (9431 / 10000 : ℝ) (9747 / 10000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_lo (3 / 2 : ℝ) (9431 / 10000 : ℝ) (9747 / 10000 : ℝ) (2333 / 1250 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (gsplit_lo (3 / 2 : ℝ) (by norm_num) (9747 / 10000 : ℝ) (9937 / 10000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_lo (3 / 2 : ℝ) (9747 / 10000 : ℝ) (9937 / 10000 : ℝ) (19323 / 10000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (piece_lo (3 / 2 : ℝ) (9937 / 10000 : ℝ) (1 : ℝ) (2477 / 1250 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)))))))))
  norm_num at h ⊢; linarith

open Checked.Trust.NCAR in
theorem gJ3_up : ∫ v in (2973 / 5000 : ℝ)..1, 2 / √((3 / 2 : ℝ) + (1 - (3 / 2 : ℝ)) * v ^ 6) ≤ (71552557 / 100000000 : ℝ) := by
  have h := (gsplit_up (3 / 2 : ℝ) (by norm_num) (2973 / 5000 : ℝ) (6897 / 10000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_up (3 / 2 : ℝ) (2973 / 5000 : ℝ) (6897 / 10000 : ℝ) (2079 / 1250 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (gsplit_up (3 / 2 : ℝ) (by norm_num) (6897 / 10000 : ℝ) (193 / 250 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_up (3 / 2 : ℝ) (6897 / 10000 : ℝ) (193 / 250 : ℝ) (16939 / 10000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (gsplit_up (3 / 2 : ℝ) (by norm_num) (193 / 250 : ℝ) (8417 / 10000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_up (3 / 2 : ℝ) (193 / 250 : ℝ) (8417 / 10000 : ℝ) (8697 / 5000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (gsplit_up (3 / 2 : ℝ) (by norm_num) (8417 / 10000 : ℝ) (8987 / 10000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_up (3 / 2 : ℝ) (8417 / 10000 : ℝ) (8987 / 10000 : ℝ) (8993 / 5000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (gsplit_up (3 / 2 : ℝ) (by norm_num) (8987 / 10000 : ℝ) (943 / 1000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_up (3 / 2 : ℝ) (8987 / 10000 : ℝ) (943 / 1000 : ℝ) (2333 / 1250 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (gsplit_up (3 / 2 : ℝ) (by norm_num) (943 / 1000 : ℝ) (9747 / 10000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_up (3 / 2 : ℝ) (943 / 1000 : ℝ) (9747 / 10000 : ℝ) (4831 / 2500 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (gsplit_up (3 / 2 : ℝ) (by norm_num) (9747 / 10000 : ℝ) (9937 / 10000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_up (3 / 2 : ℝ) (9747 / 10000 : ℝ) (9937 / 10000 : ℝ) (19817 / 10000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (piece_up (3 / 2 : ℝ) (9937 / 10000 : ℝ) (1 : ℝ) (2 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)))))))))
  norm_num at h ⊢; linarith

open Checked.Trust.NCAR in
theorem gJ5_lo : (24546067 / 25000000 : ℝ) ≤ ∫ v in (841 / 2000 : ℝ)..1, 2 / √((3 / 2 : ℝ) + (1 - (3 / 2 : ℝ)) * v ^ 6) := by
  have h := (gsplit_lo (3 / 2 : ℝ) (by norm_num) (841 / 2000 : ℝ) (1391 / 2500 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_lo (3 / 2 : ℝ) (841 / 2000 : ℝ) (1391 / 2500 : ℝ) (2043 / 1250 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (gsplit_lo (3 / 2 : ℝ) (by norm_num) (1391 / 2500 : ℝ) (6741 / 10000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_lo (3 / 2 : ℝ) (1391 / 2500 : ℝ) (6741 / 10000 : ℝ) (16411 / 10000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (gsplit_lo (3 / 2 : ℝ) (by norm_num) (6741 / 10000 : ℝ) (7737 / 10000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_lo (3 / 2 : ℝ) (6741 / 10000 : ℝ) (7737 / 10000 : ℝ) (16591 / 10000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (gsplit_lo (3 / 2 : ℝ) (by norm_num) (7737 / 10000 : ℝ) (1069 / 1250 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_lo (3 / 2 : ℝ) (7737 / 10000 : ℝ) (1069 / 1250 : ℝ) (16947 / 10000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (gsplit_lo (3 / 2 : ℝ) (by norm_num) (1069 / 1250 : ℝ) (4593 / 5000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_lo (3 / 2 : ℝ) (1069 / 1250 : ℝ) (4593 / 5000 : ℝ) (17511 / 10000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (gsplit_lo (3 / 2 : ℝ) (by norm_num) (4593 / 5000 : ℝ) (4819 / 5000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_lo (3 / 2 : ℝ) (4593 / 5000 : ℝ) (4819 / 5000 : ℝ) (913 / 500 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (gsplit_lo (3 / 2 : ℝ) (by norm_num) (4819 / 5000 : ℝ) (991 / 1000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_lo (3 / 2 : ℝ) (4819 / 5000 : ℝ) (991 / 1000 : ℝ) (763 / 400 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (piece_lo (3 / 2 : ℝ) (991 / 1000 : ℝ) (1 : ℝ) (19741 / 10000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)))))))))
  norm_num at h ⊢; linarith

open Checked.Trust.NCAR in
theorem gJ5_up : ∫ v in (1051 / 2500 : ℝ)..1, 2 / √((3 / 2 : ℝ) + (1 - (3 / 2 : ℝ)) * v ^ 6) ≤ (100371461 / 100000000 : ℝ) := by
  have h := (gsplit_up (3 / 2 : ℝ) (by norm_num) (1051 / 2500 : ℝ) (5563 / 10000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_up (3 / 2 : ℝ) (1051 / 2500 : ℝ) (5563 / 10000 : ℝ) (4103 / 2500 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (gsplit_up (3 / 2 : ℝ) (by norm_num) (5563 / 10000 : ℝ) (337 / 500 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_up (3 / 2 : ℝ) (5563 / 10000 : ℝ) (337 / 500 : ℝ) (1037 / 625 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (gsplit_up (3 / 2 : ℝ) (by norm_num) (337 / 500 : ℝ) (967 / 1250 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_up (3 / 2 : ℝ) (337 / 500 : ℝ) (967 / 1250 : ℝ) (16947 / 10000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (gsplit_up (3 / 2 : ℝ) (by norm_num) (967 / 1250 : ℝ) (8551 / 10000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_up (3 / 2 : ℝ) (967 / 1250 : ℝ) (8551 / 10000 : ℝ) (17511 / 10000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (gsplit_up (3 / 2 : ℝ) (by norm_num) (8551 / 10000 : ℝ) (1837 / 2000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_up (3 / 2 : ℝ) (8551 / 10000 : ℝ) (1837 / 2000 : ℝ) (913 / 500 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (gsplit_up (3 / 2 : ℝ) (by norm_num) (1837 / 2000 : ℝ) (4819 / 5000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_up (3 / 2 : ℝ) (1837 / 2000 : ℝ) (4819 / 5000 : ℝ) (4769 / 2500 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (gsplit_up (3 / 2 : ℝ) (by norm_num) (4819 / 5000 : ℝ) (991 / 1000 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (piece_up (3 / 2 : ℝ) (4819 / 5000 : ℝ) (991 / 1000 : ℝ) (9871 / 5000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (piece_up (3 / 2 : ℝ) (991 / 1000 : ℝ) (1 : ℝ) (2 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)))))))))
  norm_num at h ⊢; linarith

open Checked.Trust.NCAQ Checked.Trust.NCAR in
theorem Bh2_1 : (85067 / 500000 : ℝ) ≤ Bc (2 / 5 : ℝ) (31 / 10 : ℝ) ((1 / 2) * (Real.log 2 / Real.log 10)) ∧
    Bc (2 / 5 : ℝ) (31 / 10 : ℝ) ((1 / 2) * (Real.log 2 / Real.log 10)) ≤ (170161 / 1000000 : ℝ) := by
  obtain ⟨l1, l2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10
  have q2 := pow_le_pow_left₀ (by norm_num) l1 2
  have q2' := pow_le_pow_left₀ (by linarith) l2 2
  have q3 := pow_le_pow_left₀ (by norm_num) l1 3
  have q3' := pow_le_pow_left₀ (by linarith) l2 3
  unfold Bc; constructor <;> (ring_nf; ring_nf at q2 q2' q3 q3'; linarith)

open Checked.Trust.NCAQ Checked.Trust.NCAR in
theorem Bh2_3 : (818411 / 1000000 : ℝ) ≤ Bc (2 / 5 : ℝ) (31 / 10 : ℝ) ((3 / 2) * (Real.log 2 / Real.log 10)) ∧
    Bc (2 / 5 : ℝ) (31 / 10 : ℝ) ((3 / 2) * (Real.log 2 / Real.log 10)) ≤ (51163 / 62500 : ℝ) := by
  obtain ⟨l1, l2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10
  have q2 := pow_le_pow_left₀ (by norm_num) l1 2
  have q2' := pow_le_pow_left₀ (by linarith) l2 2
  have q3 := pow_le_pow_left₀ (by norm_num) l1 3
  have q3' := pow_le_pow_left₀ (by linarith) l2 3
  unfold Bc; constructor <;> (ring_nf; ring_nf at q2 q2' q3 q3'; linarith)

open Checked.Trust.NCAQ Checked.Trust.NCAR in
theorem Bh2_5 : (575027 / 250000 : ℝ) ≤ Bc (2 / 5 : ℝ) (31 / 10 : ℝ) ((5 / 2) * (Real.log 2 / Real.log 10)) ∧
    Bc (2 / 5 : ℝ) (31 / 10 : ℝ) ((5 / 2) * (Real.log 2 / Real.log 10)) ≤ (575199 / 250000 : ℝ) := by
  obtain ⟨l1, l2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10
  have q2 := pow_le_pow_left₀ (by norm_num) l1 2
  have q2' := pow_le_pow_left₀ (by linarith) l2 2
  have q3 := pow_le_pow_left₀ (by norm_num) l1 3
  have q3' := pow_le_pow_left₀ (by linarith) l2 3
  unfold Bc; constructor <;> (ring_nf; ring_nf at q2 q2' q3 q3'; linarith)


open Checked.Trust.NCAQ Checked.Trust.NCAR in
/-- At `Ω = 3/2`: the luminosity distance divided by the polynomial distance with normalisation
`H' · H₀` equals `Z J / (ln 10 / H' · B)`. -/
theorem sa_ratio (Z J L B H' : ℝ) (H₀ : ℝ) (hH₀ : 0 < H₀) (hH' : 0 < H') :
    Z / H₀ * J / (L / (H' * H₀) * B) = Z * J / (L / H' * B) := by
  rcases eq_or_ne L 0 with hL | hL
  · simp [hL]
  rcases eq_or_ne B 0 with hB | hB
  · simp [hB]
  field_simp

set_option maxHeartbeats 2000000 in
open Checked.Trust.NCAQ Checked.Trust.NCAR Checked.Cosmography.B1 in
/-- `fit_direction` without `Ω ≤ 1`: the flat model of negative cosmological constant at `Ω = 3/2`
(`NCAQ.sa`); the cubic `a₂ = 2/5`, `a₃ = 31/10` (normalisation `0.9427 H₀`) matches the three distance moduli
within 1/20 mag of zero and lies on the other side of the line. -/
theorem fit_direction_h2 : necessity% Checked.Cosmography.B1Fit.fit_direction 2 := by
  have hΩ : (1:ℝ) < 3 / 2 := by norm_num
  obtain ⟨s1, s2⟩ := sqrt2_bd
  obtain ⟨l1, l2⟩ := log10_bd
  obtain ⟨m1, m2⟩ := lam_bd
  obtain ⟨v1a, v1b⟩ := v1_bd
  obtain ⟨v3a, v3b⟩ := v3_bd
  obtain ⟨v5a, v5b⟩ := v5_bd
  obtain ⟨h0, h1, hc⟩ := tO_props (3 / 2) hΩ
  obtain ⟨ht5, -, hz5⟩ := tS_props (3 / 2) (4 * √2) hΩ (by linarith)
  obtain ⟨-, -, hz3⟩ := tS_props (3 / 2) (2 * √2) hΩ (by linarith)
  obtain ⟨-, h1O, hz1⟩ := tS_props (3 / 2) √2 hΩ (by linarith)
  obtain ⟨hp, hd, hH₀, hH⟩ := sa_hyps (3 / 2) (tO (3 / 2)) (tS (3 / 2) (4 * √2)) h0 h1 hc ht5
  have o53 := tS_anti (3 / 2) (2 * √2) (4 * √2) hΩ (by linarith) (by linarith)
  have o31 := tS_anti (3 / 2) √2 (2 * √2) hΩ (by linarith) (by linarith)
  set H₀ := hubble sa (tO (3 / 2)) with hH₀def
  set H : ℝ := 9427 / 10000 * H₀ with hHdef
  have hHp : 0 < H := by positivity
  have hJ1l : (3626869 / 12500000 : ℝ) ≤ ∫ v in √(1 / √2)..1, 2 / √((3 / 2 : ℝ) + (1 - (3 / 2 : ℝ)) * v ^ 6) :=
    le_trans gJ1_lo (gshift _ (by norm_num) (by linarith) (by norm_num at v1b ⊢; linarith) (by norm_num))
  have hJ1u : ∫ v in √(1 / √2)..1, 2 / √((3 / 2 : ℝ) + (1 - (3 / 2 : ℝ)) * v ^ 6) ≤ (29636279 / 100000000 : ℝ) :=
    le_trans (gshift _ (by norm_num) (by norm_num) (by norm_num at v1a ⊢; linarith) (by linarith)) gJ1_up
  have hJ3l : (34919097 / 50000000 : ℝ) ≤ ∫ v in √(1 / (2 * √2))..1, 2 / √((3 / 2 : ℝ) + (1 - (3 / 2 : ℝ)) * v ^ 6) :=
    le_trans gJ3_lo (gshift _ (by norm_num) (by linarith) (by norm_num at v3b ⊢; linarith) (by norm_num))
  have hJ3u : ∫ v in √(1 / (2 * √2))..1, 2 / √((3 / 2 : ℝ) + (1 - (3 / 2 : ℝ)) * v ^ 6) ≤ (71552557 / 100000000 : ℝ) :=
    le_trans (gshift _ (by norm_num) (by norm_num) (by norm_num at v3a ⊢; linarith) (by linarith)) gJ3_up
  have hJ5l : (24546067 / 25000000 : ℝ) ≤ ∫ v in √(1 / (4 * √2))..1, 2 / √((3 / 2 : ℝ) + (1 - (3 / 2 : ℝ)) * v ^ 6) :=
    le_trans gJ5_lo (gshift _ (by norm_num) (by linarith) (by norm_num at v5b ⊢; linarith) (by norm_num))
  have hJ5u : ∫ v in √(1 / (4 * √2))..1, 2 / √((3 / 2 : ℝ) + (1 - (3 / 2 : ℝ)) * v ^ 6) ≤ (100371461 / 100000000 : ℝ) :=
    le_trans (gshift _ (by norm_num) (by norm_num) (by norm_num at v5a ⊢; linarith) (by linarith)) gJ5_up
  have hm : ∀ (Z J k : ℝ) (t : ℝ) (hk : Real.log (1 + (Z - 1)) = k * Real.log 2)
      (hdist : lumDistFlat sa (tO (3 / 2)) t = Z / H₀ * J) (hz : redshift sa (tO (3 / 2)) t = Z - 1)
      (Bl Bu dl du : ℝ) (hB : Bl ≤ Bc (2 / 5 : ℝ) (31 / 10 : ℝ) (k * (Real.log 2 / Real.log 10)))
      (hB' : Bc (2 / 5 : ℝ) (31 / 10 : ℝ) (k * (Real.log 2 / Real.log 10)) ≤ Bu)
      (hdl : dl ≤ Z * J) (hdu : Z * J ≤ du) (hBl : 0 < Bl)
      (c1 : 0.98 * (2.30268 / (9427 / 10000) * Bu) ≤ dl) (c2 : du ≤ 1.02 * (2.30249 / (9427 / 10000) * Bl)),
      0 < logPolyDL3 (2 / 5 : ℝ) (31 / 10 : ℝ) H (redshift sa (tO (3 / 2)) t) ∧
      |5 * Real.logb 10 (lumDistFlat sa (tO (3 / 2)) t / logPolyDL3 (2 / 5 : ℝ) (31 / 10 : ℝ) H
        (redshift sa (tO (3 / 2)) t)) - 0| ≤ 1 / 20 := by
    intro Z J k t hk hdist hz Bl Bu dl du hB hB' hdl hdu hBl c1 c2
    have hP : logPolyDL3 (2 / 5 : ℝ) (31 / 10 : ℝ) H (redshift sa (tO (3 / 2)) t)
        = Real.log 10 / H * Bc (2 / 5 : ℝ) (31 / 10 : ℝ) (k * (Real.log 2 / Real.log 10)) := by
      rw [hz, poly3_eq _ _ _ k _ hk]
    refine ⟨by rw [hP]; exact pos_of _ _ _ _ _ hHp l1 hB (by norm_num) hBl, ?_⟩
    rw [hP, hdist, hHdef, sa_ratio _ _ _ _ _ _ hH₀ (by norm_num)]
    exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 hB hB' hdl hdu (by norm_num) hBl c1 c2
  have hk1 : Real.log (1 + (√2 - 1)) = 1 / 2 * Real.log 2 := log_s2
  have hk3 : Real.log (1 + (2 * √2 - 1)) = 3 / 2 * Real.log 2 := log_2s2
  have hk5 : Real.log (1 + (4 * √2 - 1)) = 5 / 2 * Real.log 2 := log_4s2
  have hD1 := sa_dL (3 / 2) √2 hΩ (by linarith)
  have hD3 := sa_dL (3 / 2) (2 * √2) hΩ (by linarith)
  have hD5 := sa_dL (3 / 2) (4 * √2) hΩ (by linarith)
  obtain ⟨p1, r1⟩ := hm √2 _ (1 / 2) _ hk1 hD1 hz1 _ _ (1.41421 * (3626869 / 12500000 : ℝ))
    (1.41422 * (29636279 / 100000000 : ℝ)) Bh2_1.1 Bh2_1.2
    (mul_le_mul s1 hJ1l (by norm_num) (by linarith)) (mul_le_mul s2 hJ1u (by linarith) (by norm_num))
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨p3, r3⟩ := hm (2 * √2) _ (3 / 2) _ hk3 hD3 hz3 _ _ (2 * 1.41421 * (34919097 / 50000000 : ℝ))
    (2 * 1.41422 * (71552557 / 100000000 : ℝ)) Bh2_3.1 Bh2_3.2
    (mul_le_mul (by linarith) hJ3l (by norm_num) (by linarith))
    (mul_le_mul (by linarith) hJ3u (by linarith) (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨p5, r5⟩ := hm (4 * √2) _ (5 / 2) _ hk5 hD5 hz5 _ _ (4 * 1.41421 * (24546067 / 25000000 : ℝ))
    (4 * 1.41422 * (100371461 / 100000000 : ℝ)) Bh2_5.1 Bh2_5.2
    (mul_le_mul (by linarith) hJ5l (by norm_num) (by linarith))
    (mul_le_mul (by linarith) hJ5u (by linarith) (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨3 / 2, by norm_num, sa, _, _, _, tO (3 / 2), o53, o31, h1O, hp, hd, hH₀, hH, hz1, hz3, hz5,
    (2 / 5 : ℝ), (31 / 10 : ℝ), H, 0, hHp, p1, p3, p5, r1, r3, r5, ?_⟩
  rw [not_lt]
  unfold lusA2 lusA3
  have hlb : Real.logb 10 2 = Real.log 2 / Real.log 10 := rfl
  rw [hlb]
  have hsq2 : Real.log 10 ^ 2 ≤ (2.30268 : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) l2 2
  have hsq1 : (2.30249 : ℝ) ^ 2 ≤ Real.log 10 ^ 2 := pow_le_pow_left₀ (by norm_num) l1 2
  set lam := Real.log 2 / Real.log 10
  have e1 : 9 / 8 * (3 / 2 : ℝ) ^ 2 - 2 * (3 / 2) + 7 / 6 = 67 / 96 := by norm_num
  have e2 : (3 / 2 : ℝ) - 3 / 4 * (3 / 2) = 3 / 8 := by norm_num
  rw [e1, e2]
  have hA3 : (2.30249 : ℝ) ^ 2 * (67 / 96) ≤ Real.log 10 ^ 2 * (67 / 96) :=
    mul_le_mul_of_nonneg_right hsq1 (by norm_num)
  have hneg : 31 / 10 - Real.log 10 ^ 2 * (67 / 96) ≤ 31 / 10 - (2.30249 : ℝ) ^ 2 * (67 / 96) := by linarith
  have hlam : 0 ≤ 20 / 3 * lam := by linarith
  have hx : 20 / 3 * lam * (31 / 10 - Real.log 10 ^ 2 * (67 / 96))
      ≤ 20 / 3 * lam * (31 / 10 - (2.30249 : ℝ) ^ 2 * (67 / 96)) := mul_le_mul_of_nonneg_left hneg hlam
  norm_num at hx ⊢
  nlinarith

end Checked.Trust.NCAS
