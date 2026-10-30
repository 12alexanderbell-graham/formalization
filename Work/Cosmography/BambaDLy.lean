import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Checked.Cosmography.CCSLookback

/-!
# Candidate C5: Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012),
arXiv:1205.3421v3, Sec. X, Eqs. (10.52)–(10.54)

Source (typeset text verified by rendering the PDF, runs 2026-10-30T0628Z and 2026-10-30T0828Z;
`runs/2026-10-30T0628Z/screen_bamba/crop_p111_eq10.54-57_DLy.png`), p. 110–111:
"We define Ω₀ = 1 + Kc²/(H₀²a₀²), which can be considered a purely cosmographic parameter [...]
With these parameters, we obtain D⁰_{L,y} = 1 (10.52), D¹_{L,y} = −½(−3 + q₀) (10.53),
D²_{L,y} = −⅙(12 − 5q₀ + 3q₀² − j₀ − Ω₀) (10.54) [...] Previous relations have been derived for
any value of the curvature parameter."
The series these coefficients belong to is not printed for `y`; by analogy with (10.38)
`d_L(z) = (cz/H₀)[D⁰_L + D¹_L z + ... + O(z⁵)]` it is `d_L(y) = (cy/H₀)[D⁰_{L,y} + D¹_{L,y} y +
D²_{L,y} y² + ...]`, with `y = z/(1+z)` (the y-redshift of Cattoën–Visser 2007, arXiv:0710.1887,
whose Eq. (52) the review reproduces). Reading recorded as Underspecified (annex 40.4); the printed
`D¹_{L,y}` is right only for this reading (`D¹_{L,y} = 1 + D¹_L`).

Conventions (as `Checked.Cosmography`): `hubble a t = ȧ/a`, `decel a t = −ä a/ȧ²`,
`cosmoCoeff 3 a t = a⃛/(a H³)` (= j), `redshift a t₀ t = a(t₀)/a(t) − 1`, `c = 1`.
Spatially flat FLRW (`K = 0`, so `Ω₀ = 1`): comoving distance `χ(t) = ∫_t^{t₀} dt'/a(t')`,
luminosity distance `d_L = a₀ (1 + z) χ`.

We test the flat instance of the claim (`Ω₀ = 1`). A claim made "for any value of the curvature
parameter" is false if its flat instance is false.

FROZEN (annex 40.1) in run 2026-10-30T0828Z before proof work.
-/

namespace Work.Cosmography.BambaY

open Filter Asymptotics Topology Checked.Cosmography Checked.Cosmography.Aviles
open scoped ContDiff

/-- The y-redshift `y = z/(1+z)`. -/
noncomputable def yred (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  redshift a t₀ t / (1 + redshift a t₀ t)

/-- Comoving radial distance `χ = ∫_t^{t₀} c dt'/a(t')` (`c = 1`). -/
noncomputable def comoving (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  ∫ s in t..t₀, 1 / a s

/-- Luminosity distance in a spatially flat FLRW model: `d_L = a₀ (1 + z) χ` (`c = 1`). -/
noncomputable def lumDistFlat (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  a t₀ * (1 + redshift a t₀ t) * comoving a t₀ t

/-- `D¹_{L,y}` as printed (Eq. (10.53)). -/
noncomputable def D1y (q : ℝ) : ℝ := -(1 / 2) * (-3 + q)

/-- `D²_{L,y}` as printed (Eq. (10.54)), verbatim. -/
noncomputable def printedD2y (q j Ω : ℝ) : ℝ := -(1 / 6) * (12 - 5 * q + 3 * q ^ 2 - j - Ω)

/-- `D²_{L,y}` with the overall sign `+` (Cattoën–Visser 2007 Eq. (52)). -/
noncomputable def correctD2y (q j Ω : ℝ) : ℝ := (1 / 6) * (12 - 5 * q + 3 * q ^ 2 - j - Ω)

/-- `H₀ d_L(y)/c = y [1 + D¹ y + D² y²]` with a given `D²`. -/
noncomputable def seriesY (d2 q y : ℝ) : ℝ :=
  y * (1 + D1y q * y + d2 * y ^ 2)

/-- Remainder `H₀ d_L − y[1 + D¹y + D²y²]` in a flat model (`Ω₀ = 1`), for a choice of `D²`. -/
noncomputable def remainderY (D2 : ℝ → ℝ → ℝ → ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  hubble a t₀ * lumDistFlat a t₀ t -
    seriesY (D2 (decel a t₀) (cosmoCoeff 3 a t₀) 1) (decel a t₀) (yred a t₀ t)

/-- The printed claim, flat instance, weakest reading (`o(y³)`), strongest hypotheses (analytic,
everywhere positive scale factor, `H₀ > 0`). -/
def BambaD2yClaim : Prop :=
  ∀ (a : ℝ → ℝ) (t₀ : ℝ), ContDiff ℝ ω a → (∀ t, 0 < a t) → 0 < hubble a t₀ →
    (fun t => remainderY printedD2y a t₀ t) =o[𝓝 t₀] (fun t => yred a t₀ t ^ 3)

/-- Same, past emission only (`t < t₀`). -/
def BambaD2yClaimPast : Prop :=
  ∀ (a : ℝ → ℝ) (t₀ : ℝ), ContDiff ℝ ω a → (∀ t, 0 < a t) → 0 < hubble a t₀ →
    (fun t => remainderY printedD2y a t₀ t) =o[𝓝[<] t₀] (fun t => yred a t₀ t ^ 3)

/-- **Luminosity distance to third order in `y`** (flat FLRW, correct `D²_{L,y}`): for every
scale factor that is `C³` at `t₀`, with `a(t₀) ≠ 0` and `H₀ ≠ 0`. -/
theorem lumDist_y_third_order (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 3 a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0) :
    (fun t => remainderY correctD2y a t₀ t) =o[𝓝 t₀] (fun t => yred a t₀ t ^ 3) := by
  sorry

/-- The printed `D²_{L,y}` fails in every flat `C³` model with `a(t₀) ≠ 0`, `H₀ ≠ 0` and
`11 − 5q₀ + 3q₀² − j₀ ≠ 0` (past emission only; the two-sided version follows). -/
theorem printedD2y_fails_past (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 3 a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0)
    (hD : 11 - 5 * decel a t₀ + 3 * decel a t₀ ^ 2 - cosmoCoeff 3 a t₀ ≠ 0) :
    ¬ (fun t => remainderY printedD2y a t₀ t) =o[𝓝[<] t₀] (fun t => yred a t₀ t ^ 3) := by
  sorry

/-- Two-sided version. -/
theorem printedD2y_fails (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 3 a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0)
    (hD : 11 - 5 * decel a t₀ + 3 * decel a t₀ ^ 2 - cosmoCoeff 3 a t₀ ≠ 0) :
    ¬ (fun t => remainderY printedD2y a t₀ t) =o[𝓝 t₀] (fun t => yred a t₀ t ^ 3) := by
  sorry

/-- The printed claim is false (witness: flat de Sitter, `a = exp`, `t₀ = 0`). -/
theorem bambaD2yClaim_false : ¬ BambaD2yClaim := by
  sorry

/-- The past-only reading is false (flat de Sitter). -/
theorem bambaD2yClaimPast_false : ¬ BambaD2yClaimPast := by
  sorry

end Work.Cosmography.BambaY
