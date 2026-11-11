import Checked.Trust.NonVacuity
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Checked.Cosmography.B1Fit
import Checked.Cosmography.B1FitCerts
import Checked.Cosmography.B1FitRL19
import Checked.Cosmography.B1FitTools
import Checked.Cosmography.B1FitWitness
import Checked.Cosmography.B1L19
import Checked.Cosmography.B1L19Certs
import Checked.Cosmography.B1SepWitness
import Checked.Cosmography.B1Separation
import Checked.Cosmography.B1Truncation
import Checked.Cosmography.BambaAngular
import Checked.Cosmography.BambaCurved
import Checked.Cosmography.BambaDLy
import Checked.Cosmography.BambaZ
import Checked.Cosmography.CCSLookback
import Checked.Cosmography.CPLCoefficients
import Checked.Cosmography.CPLExistence
import Checked.Cosmography.CVdQ
import Checked.Cosmography.DemianskiZ
import Checked.Cosmography.FRCosmo
import Checked.Cosmography.FREta
import Checked.Cosmography.LCDMCoefficients
import Checked.Cosmography.LCDMWitness
import Checked.Cosmography.Lookback
import Checked.Cosmography.LookbackThird
import Checked.Cosmography.Transverse

open Filter Topology
namespace Checked.Trust.NCB
open Checked.Cosmography
/-- The scale factor 1 + t² (zero velocity at t = 0). -/
noncomputable def flatStart (t : ℝ) : ℝ := 1 + t ^ 2

theorem flatStart_deriv : deriv flatStart = fun t => 2 * t := by
  funext t
  have h : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * t) t := by
    simpa using (hasDerivAt_pow 2 t).const_add 1
  exact h.deriv


section SeriesHubble
open Checked.Cosmography Checked.Cosmography.Aviles Asymptotics

/-! ### A nonzero Hubble rate is needed in the cosmographic series (run 2026-11-11T0028Z)

With the scale factor 1 + t² at t₀ = 0 the velocity, hence the Hubble rate, is 0, every junk
coefficient (deceleration, jerk, …) is 0, and each remainder `H₀ · distance − x (1 + c₁ x + …)`
reduces to −x(1 + c₁x + …), which is of exact order x, not o(xⁿ) for n ≥ 2 (`x` is the redshift
z = −t²/(1 + t²) or y = z/(1 + z) = −t²). -/

/-- Core: −x·g(x) with g → 1 is not o(xⁿ), n ≥ 2, where x → 0 and x ≠ 0 frequently. -/
theorem not_littleO_core (x g : ℝ → ℝ) (t₀ H : ℝ) (D : ℝ → ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hH : H = 0) (hx : Tendsto x (𝓝 t₀) (𝓝 0)) (hg : ContinuousAt g 0) (hg0 : g 0 = 1)
    (hfreq : ∃ᶠ t in 𝓝 t₀, x t ≠ 0) :
    ¬ (fun t => H * D t - x t * g (x t)) =o[𝓝 t₀] (fun t => x t ^ n) := by
  intro h
  subst hH
  have h1 := h.bound (show (0 : ℝ) < 1 / 4 by norm_num)
  have h2 : ∀ᶠ t in 𝓝 t₀, |g (x t) - 1| < 1 / 2 := by
    have := Metric.tendsto_nhds.1 ((hg.tendsto.comp hx)) (1 / 2) (by norm_num)
    simpa [Real.dist_eq, hg0] using this
  have h3 : ∀ᶠ t in 𝓝 t₀, |x t| < 1 := by
    have := Metric.tendsto_nhds.1 hx 1 one_pos
    simpa [Real.dist_eq] using this
  apply hfreq
  filter_upwards [h1, h2, h3] with t ht1 ht2 ht3
  simp only [zero_mul, zero_sub, norm_neg, norm_mul, Real.norm_eq_abs, abs_pow] at ht1
  have hxn : |x t| ^ n ≤ |x t| := by
    calc |x t| ^ n ≤ |x t| ^ 1 := pow_le_pow_of_le_one (abs_nonneg _) ht3.le (by omega)
      _ = |x t| := pow_one _
  have hg' : 1 / 2 ≤ |g (x t)| := by
    have := abs_sub_abs_le_abs_sub 1 (g (x t)); rw [abs_sub_comm] at this; norm_num at this; linarith
  have : |x t| * (1 / 2) ≤ |x t| * (1 / 4) := by
    calc |x t| * (1 / 2) ≤ |x t| * |g (x t)| := mul_le_mul_of_nonneg_left hg' (abs_nonneg _)
      _ ≤ 1 / 4 * |x t| ^ n := ht1
      _ ≤ 1 / 4 * |x t| := by gcongr
      _ = |x t| * (1 / 4) := by ring
  have : |x t| ≤ 0 := by nlinarith [abs_nonneg (x t)]
  exact not_not.2 (abs_nonpos_iff.1 this)

theorem not_littleO_deg4 (x : ℝ → ℝ) (t₀ H c₁ c₂ c₃ c₄ : ℝ) (D : ℝ → ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hH : H = 0) (hx : Tendsto x (𝓝 t₀) (𝓝 0)) (hfreq : ∃ᶠ t in 𝓝 t₀, x t ≠ 0) :
    ¬ (fun t => H * D t - x t * (1 + c₁ * x t + c₂ * x t ^ 2 + c₃ * x t ^ 3 + c₄ * x t ^ 4))
      =o[𝓝 t₀] (fun t => x t ^ n) :=
  not_littleO_core x (fun z => 1 + c₁ * z + c₂ * z ^ 2 + c₃ * z ^ 3 + c₄ * z ^ 4) t₀ H D n hn hH hx
    (by fun_prop) (by simp) hfreq

theorem not_littleO_deg2 (x : ℝ → ℝ) (t₀ H c₁ c₂ : ℝ) (D : ℝ → ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hH : H = 0) (hx : Tendsto x (𝓝 t₀) (𝓝 0)) (hfreq : ∃ᶠ t in 𝓝 t₀, x t ≠ 0) :
    ¬ (fun t => H * D t - x t * (1 + c₁ * x t + c₂ * x t ^ 2)) =o[𝓝 t₀] (fun t => x t ^ n) :=
  not_littleO_core x (fun z => 1 + c₁ * z + c₂ * z ^ 2) t₀ H D n hn hH hx (by fun_prop) (by simp) hfreq

theorem not_littleO_deg2m (x : ℝ → ℝ) (t₀ H c₁ c₂ : ℝ) (D : ℝ → ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hH : H = 0) (hx : Tendsto x (𝓝 t₀) (𝓝 0)) (hfreq : ∃ᶠ t in 𝓝 t₀, x t ≠ 0) :
    ¬ (fun t => H * D t - x t * (1 - c₁ * x t + c₂ * x t ^ 2)) =o[𝓝 t₀] (fun t => x t ^ n) :=
  not_littleO_core x (fun z => 1 - c₁ * z + c₂ * z ^ 2) t₀ H D n hn hH hx (by fun_prop) (by simp) hfreq

theorem flatStart_hubble : hubble flatStart 0 = 0 := by
  simp [hubble, flatStart_deriv]

theorem flatStart_redshift (t : ℝ) : redshift flatStart 0 t = -(t ^ 2 / (1 + t ^ 2)) := by
  simp [redshift, flatStart]; field_simp; ring

theorem flatStart_yred (t : ℝ) : Checked.Cosmography.BambaY.yred flatStart 0 t = -t ^ 2 := by
  simp only [Checked.Cosmography.BambaY.yred, flatStart_redshift]
  have h1 : (0 : ℝ) < 1 + t ^ 2 := by positivity
  field_simp
  ring

theorem flatStart_z_tendsto : Tendsto (fun t => redshift flatStart 0 t) (𝓝 0) (𝓝 0) := by
  simp only [flatStart_redshift]
  have : Continuous fun t : ℝ => -(t ^ 2 / (1 + t ^ 2)) :=
    by exact (continuous_pow 2 |>.div (continuous_const.add (continuous_pow 2)) (fun t => (by positivity : (0:ℝ) < 1 + t ^ 2).ne')).neg
  simpa using this.tendsto 0

theorem flatStart_y_tendsto : Tendsto (fun t => Checked.Cosmography.BambaY.yred flatStart 0 t) (𝓝 0) (𝓝 0) := by
  simp only [flatStart_yred]
  have : Continuous fun t : ℝ => -t ^ 2 := by fun_prop
  simpa using this.tendsto 0

theorem frequently_ne_of_ne (x : ℝ → ℝ) (hx : ∀ t, t ≠ 0 → x t ≠ 0) : ∃ᶠ t in 𝓝 (0 : ℝ), x t ≠ 0 := by
  intro h
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.1 h
  have : dist (δ / 2) 0 < δ := by rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith
  exact hb this (hx _ (by positivity))

theorem flatStart_z_freq : ∃ᶠ t in 𝓝 (0 : ℝ), redshift flatStart 0 t ≠ 0 :=
  frequently_ne_of_ne _ fun t ht => by
    rw [flatStart_redshift]; have : 0 < t ^ 2 := by positivity
    exact neg_ne_zero.2 (div_pos this (by positivity)).ne'

theorem flatStart_y_freq : ∃ᶠ t in 𝓝 (0 : ℝ), Checked.Cosmography.BambaY.yred flatStart 0 t ≠ 0 :=
  frequently_ne_of_ne _ fun t ht => by rw [flatStart_yred]; exact neg_ne_zero.2 (pow_ne_zero 2 ht)

theorem flatStart_smooth (n : WithTop ℕ∞) : ContDiffAt ℝ n flatStart 0 :=
  (show ContDiff ℝ n flatStart from ContDiff.add contDiff_const (contDiff_id.pow 2)).contDiffAt

theorem flatStart_ne : flatStart 0 ≠ 0 := by simp [flatStart]

/-- A nonzero Hubble rate is needed in the fifth-order lookback series (scale factor 1 + t²). -/
theorem lookback_fifth_order_h3 : necessity% Checked.Cosmography.CCS.lookback_fifth_order 3 := by
  refine ⟨flatStart, 0, flatStart_smooth _, flatStart_ne, ?_⟩
  unfold Checked.Cosmography.CCS.remainder Checked.Cosmography.CCS.series
  exact not_littleO_deg4 _ _ _ _ _ _ _ _ 5 (by norm_num) flatStart_hubble flatStart_z_tendsto flatStart_z_freq

/-- A nonzero Hubble rate is needed in the third-order luminosity-distance series in y. -/
theorem lumDist_y_third_order_h3 : necessity% Checked.Cosmography.BambaY.lumDist_y_third_order 3 := by
  refine ⟨flatStart, 0, flatStart_smooth _, flatStart_ne, ?_⟩
  unfold Checked.Cosmography.BambaY.remainderY Checked.Cosmography.BambaY.seriesY
  exact not_littleO_deg2 _ _ _ _ _ _ 3 (by norm_num) flatStart_hubble flatStart_y_tendsto flatStart_y_freq

/-- A nonzero Hubble rate is needed in the third-order deceleration-distance series in y. -/
theorem dQ_y_third_order_h3 : necessity% Checked.Cosmography.CVdQ.dQ_y_third_order 3 := by
  refine ⟨flatStart, 0, flatStart_smooth _, flatStart_ne, ?_⟩
  unfold Checked.Cosmography.CVdQ.remainderQ Checked.Cosmography.CVdQ.seriesQ
  exact not_littleO_deg2m _ _ _ _ _ _ 3 (by norm_num) flatStart_hubble flatStart_y_tendsto flatStart_y_freq

/-- A nonzero Hubble rate is needed in the fifth-order curved luminosity-distance series in y. -/
theorem lumDist_y_fifth_order_h3 : necessity% Checked.Cosmography.BambaK.lumDist_y_fifth_order 3 := by
  refine ⟨0, flatStart, 0, flatStart_smooth _, flatStart_ne, ?_⟩
  unfold Checked.Cosmography.BambaK.remK Checked.Cosmography.BambaK.seriesY4
  exact not_littleO_deg4 _ _ _ _ _ _ _ _ 5 (by norm_num) flatStart_hubble flatStart_y_tendsto flatStart_y_freq

/-- A nonzero Hubble rate is needed in the fifth-order angular-distance series in y. -/
theorem angDist_y_fifth_order_h3 : necessity% Checked.Cosmography.BambaA.angDist_y_fifth_order 3 := by
  refine ⟨0, flatStart, 0, flatStart_smooth _, flatStart_ne, ?_⟩
  unfold Checked.Cosmography.BambaA.remA
  exact not_littleO_deg4 _ _ _ _ _ _ _ _ 5 (by norm_num) flatStart_hubble flatStart_y_tendsto flatStart_y_freq

/-- A nonzero Hubble rate is needed in the fifth-order luminosity-distance series in z. -/
theorem lumDist_z_fifth_order_h3 : necessity% Checked.Cosmography.BambaZ.lumDist_z_fifth_order 3 := by
  refine ⟨0, flatStart, 0, flatStart_smooth _, flatStart_ne, ?_⟩
  unfold Checked.Cosmography.BambaZ.remLz Checked.Cosmography.BambaZ.seriesZ
  exact not_littleO_deg4 _ _ _ _ _ _ _ _ 5 (by norm_num) flatStart_hubble flatStart_z_tendsto flatStart_z_freq

/-- A nonzero Hubble rate is needed in the fifth-order angular-distance series in z. -/
theorem angDist_z_fifth_order_h3 : necessity% Checked.Cosmography.BambaZ.angDist_z_fifth_order 3 := by
  refine ⟨0, flatStart, 0, flatStart_smooth _, flatStart_ne, ?_⟩
  unfold Checked.Cosmography.BambaZ.remAz Checked.Cosmography.BambaZ.seriesZ
  exact not_littleO_deg4 _ _ _ _ _ _ _ _ 5 (by norm_num) flatStart_hubble flatStart_z_tendsto flatStart_z_freq

end SeriesHubble

end Checked.Trust.NCB
