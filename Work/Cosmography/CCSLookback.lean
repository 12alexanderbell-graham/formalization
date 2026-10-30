import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Checked.Cosmography.LCDMCoefficients

/-!
# Candidate C3: Capozziello, Cardone, Salzano, PRD 78, 063504 (2008), arXiv:0802.1583v2, Eq. (A2)

Source (typeset text verified by rendering the PDF, runs 2026-10-30T0220Z and 2026-10-30T0628Z;
`runs/2026-10-30T0628Z/typeset/`):
"a(t)/a(t₀) = 1 + H₀(t−t₀) − q₀/2 H₀²(t−t₀)² + j₀/3! H₀³(t−t₀)³ + s₀/4! H₀⁴(t−t₀)⁴
 + l₀/5! H₀⁵(t−t₀)⁵ + O[(t−t₀)⁶] (A1) [...] z = a(t₀)/a(t) − 1. The physical distance
 travelled by a photon that is emitted at time t* and absorbed at the current epoch t₀ is
 D = c ∫dt = c(t₀ − t*) [...] Solving with respect to D up to the fifth order in z gives us the
 desired expansion for D(z) as: D(z) = (cz/H₀)[D⁰ + D¹z + D²z² + D³z³ + D⁴z⁴] (A2) with
 D⁰ = 1, D¹ = −(1 + q₀/2), D² = 1 + q₀ + q₀²/2 − j₀/6,
 D³ = −(1 + 3/2 q₀ + 3/2 q₀² + 5/8 q₀³ − 1/2 j₀ − 5/12 q₀j₀ − s₀/24),
 D⁴ = 1 + 2q₀ + 3q₀² + 5/2 q₀³ + 7/2 q₀⁴ − 5/3 q₀j₀ − 7/8 q₀²j₀ − j₀ + j₀²/12 − 1/8 q₀s₀
      − s₀/6 − l₀/120."

Conventions: as `Checked.Cosmography` / `Checked.Cosmography.Aviles`: `hubble a t = ȧ/a`,
`decel a t = −ä a/ȧ²`, `cosmoCoeff n a t = a⁽ⁿ⁾/(a Hⁿ)` (j₀, s₀, l₀ for n = 3, 4, 5; the
paper's Eq. (1) definitions, matching the signs in (A1)), `redshift a t₀ t = a(t₀)/a(t) − 1`.
`H₀ D / c = H₀ (t₀ − t*)`, so `c` drops out: the claim is about lookback time in units 1/H₀.

Reading of "up to the fifth order in z" (Underspecified, recorded in the audit): the weakest
reading consistent with the printed coefficients is a remainder `o(z⁵)` as the emission time
tends to `t₀`; any stronger reading (`O(z⁶)`) implies it. We refute the weakest reading under
the strongest smoothness hypothesis (a analytic, positive everywhere).

FROZEN (annex 40.1) in run 2026-10-30T0628Z before proof work.
-/

namespace Work.Cosmography.CCS

open Filter Asymptotics Topology Checked.Cosmography Checked.Cosmography.Aviles
open scoped ContDiff

/-- `D¹` as printed (Eq. (A2)). -/
noncomputable def D1 (q : ℝ) : ℝ := -(1 + q / 2)

/-- `D²` as printed. -/
noncomputable def D2 (q j : ℝ) : ℝ := 1 + q + q ^ 2 / 2 - j / 6

/-- `D³` as printed. -/
noncomputable def D3 (q j s : ℝ) : ℝ :=
  -(1 + 3 / 2 * q + 3 / 2 * q ^ 2 + 5 / 8 * q ^ 3 - 1 / 2 * j - 5 / 12 * q * j - s / 24)

/-- `D⁴` as printed (verbatim). -/
noncomputable def printedD4 (q j s l : ℝ) : ℝ :=
  1 + 2 * q + 3 * q ^ 2 + 5 / 2 * q ^ 3 + 7 / 2 * q ^ 4
    - 5 / 3 * q * j - 7 / 8 * q ^ 2 * j - j + j ^ 2 / 12
    - 1 / 8 * q * s - s / 6 - l / 120

/-- `D⁴` with `7/8 q₀⁴` in place of the printed `7/2 q₀⁴`. -/
noncomputable def correctD4 (q j s l : ℝ) : ℝ :=
  1 + 2 * q + 3 * q ^ 2 + 5 / 2 * q ^ 3 + 7 / 8 * q ^ 4
    - 5 / 3 * q * j - 7 / 8 * q ^ 2 * j - j + j ^ 2 / 12
    - 1 / 8 * q * s - s / 6 - l / 120

/-- `H₀ D(z) / c = z [1 + D¹ z + D² z² + D³ z³ + D⁴ z⁴]` with a given `D⁴`. -/
noncomputable def series (d4 q j s z : ℝ) : ℝ :=
  z * (1 + D1 q * z + D2 q j * z ^ 2 + D3 q j s * z ^ 3 + d4 * z ^ 4)

/-- The remainder `H₀ (t₀ − t) − H₀ D(z(t))/c` for a scale factor `a` and a choice of `D⁴`. -/
noncomputable def remainder (D4 : ℝ → ℝ → ℝ → ℝ → ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  hubble a t₀ * (t₀ - t) -
    series (D4 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀))
      (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (redshift a t₀ t)

/-- The printed claim, weakest reading, strongest hypotheses: for every analytic, everywhere
positive scale factor with `H₀ > 0`, Eq. (A2) holds with remainder `o(z⁵)`. -/
def CCSD4Claim : Prop :=
  ∀ (a : ℝ → ℝ) (t₀ : ℝ), ContDiff ℝ ω a → (∀ t, 0 < a t) → 0 < hubble a t₀ →
    (fun t => remainder printedD4 a t₀ t) =o[𝓝 t₀] (fun t => redshift a t₀ t ^ 5)

/-- **Lookback time to fifth order in redshift** (correct version of Eq. (A2)): for every
scale factor that is `C⁵` at `t₀`, with `a(t₀) ≠ 0` and `H₀ ≠ 0`. -/
theorem lookback_fifth_order (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 5 a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0) :
    (fun t => remainder correctD4 a t₀ t) =o[𝓝 t₀] (fun t => redshift a t₀ t ^ 5) := by
  sorry

/-- The printed `D⁴` fails for every `C⁵` scale factor with `a(t₀) ≠ 0`, `H₀ ≠ 0`, `q₀ ≠ 0`. -/
theorem printedD4_fails (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 5 a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0) (hq : decel a t₀ ≠ 0) :
    ¬ (fun t => remainder printedD4 a t₀ t) =o[𝓝 t₀] (fun t => redshift a t₀ t ^ 5) := by
  sorry

/-- The printed claim is false (witness: de Sitter, `a = exp`, `t₀ = 0`). -/
theorem ccsD4Claim_false : ¬ CCSD4Claim := by
  sorry

end Work.Cosmography.CCS
