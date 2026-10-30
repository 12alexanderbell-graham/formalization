import Work.Cosmography.Transverse
import Checked.Cosmography.CCSLookback

/-!
# Candidate C6: Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012),
arXiv:1205.3421v3, Sec. X, Eqs. (10.55)–(10.57): curvature terms of `D³_{L,y}`, `D⁴_{L,y}`

Source (typeset text verified by rendering the PDF; `runs/2026-10-30T0828Z/typeset/
crop_p111_eq10.54-57_DLy.png`, transcription `runs/2026-10-30T1028Z/source_C6.md`):
"D³_{L,y} = (1/24)[52 − 20q₀ + 21q₀² − 15q₀³ − 7j₀ + 10q₀j₀ + s₀ − 2Ω₀(1 + 3q₀)] (10.55),
D⁴_{L,y} = (1/120)[359 − 184q₀ + 186q₀² − 135q₀³ + 105q₀⁴ + 90q₀j₀ − 105q₀²j₀ − 15q₀s₀ +
− 57j₀ + 10j² + 9s₀ − l₀ − 5Ω₀(17 − 6q₀ + 9q₀² − 2j₀)] (10.56)–(10.57)"
with "Ω₀ = 1 + Kc²/(H₀²a₀²)" (p. 110), d_L = (a₀/a(t)) a₀ r₀ (10.26), r₀ = sin / identity / sinh
of `∫ c dt/a` for K = +1 / 0 / −1 (10.28), and "Previous relations have been derived for any value
of the curvature parameter." The `j²` in (10.57) is read as `j₀²`.

Reading (as C5, Underspecified, annex 40.4): `d_L(y) = (c y/H₀)[1 + D¹ y + D² y² + D³ y³ + D⁴ y⁴
+ O(y⁵)]`, `y = z/(1+z)`.

Charitable claims. `D²_{L,y}` is printed with the wrong overall sign (finding F4, already PROVED);
to test (10.55) on its own we use the CORRECTED `D²` (`BambaY.correctD2y`), and to test
(10.56)–(10.57) on their own we also use the corrected `D³` below. A claim is false if it fails for
some model; we state it for every analytic, everywhere positive scale factor with `H₀ > 0` and every
real curvature constant `K` (K = ±1 are instances; `transverse K` is `sin(√K χ)/√K`, `χ`,
`sinh(√−K χ)/√−K`).

Conventions (as `Checked.Cosmography`): `c = 1`, `hubble a t = ȧ/a`, `decel a t = −ä a/ȧ²`,
`cosmoCoeff n a t = a⁽ⁿ⁾/(a Hⁿ)` (j, s, l for n = 3, 4, 5), `redshift a t₀ t = a(t₀)/a(t) − 1`,
`comoving a t₀ t = ∫_t^{t₀} dt'/a(t')`.

FROZEN (annex 40.1) in run 2026-10-30T1028Z before proof work.
-/

namespace Work.Cosmography.BambaK

open Filter Asymptotics Topology Checked.Cosmography Checked.Cosmography.Aviles
open Checked.Cosmography.BambaY Work.Cosmography.Transverse
open scoped ContDiff

/-- `Ω₀ = 1 + K c²/(H₀² a₀²)` (`c = 1`). -/
noncomputable def omega0 (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) : ℝ :=
  1 + K / (hubble a t₀ ^ 2 * a t₀ ^ 2)

/-- Luminosity distance in FLRW with curvature constant `K`: `d_L = a₀ (1 + z) S_K(χ)`
(Eqs. (10.26), (10.28), `c = 1`). -/
noncomputable def lumDist (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  a t₀ * (1 + redshift a t₀ t) * transverse K (comoving a t₀ t)

/-- `D³_{L,y}` as printed (Eq. (10.55)), verbatim. -/
noncomputable def printedD3y (q j s Ω : ℝ) : ℝ :=
  (1 / 24) * (52 - 20 * q + 21 * q ^ 2 - 15 * q ^ 3 - 7 * j + 10 * q * j + s - 2 * Ω * (1 + 3 * q))

/-- `D⁴_{L,y}` as printed (Eqs. (10.56)–(10.57)), verbatim (`j² = j₀²`). -/
noncomputable def printedD4y (q j s l Ω : ℝ) : ℝ :=
  (1 / 120) * (359 - 184 * q + 186 * q ^ 2 - 135 * q ^ 3 + 105 * q ^ 4 + 90 * q * j
    - 105 * q ^ 2 * j - 15 * q * s + -57 * j + 10 * j ^ 2 + 9 * s - l
    - 5 * Ω * (17 - 6 * q + 9 * q ^ 2 - 2 * j))

/-- Proposed correction of (10.55): add `(Ω₀ − 1)(3q₀ − 2)/6` (zero when flat). -/
noncomputable def correctD3y (q j s Ω : ℝ) : ℝ :=
  printedD3y q j s Ω + (Ω - 1) * (3 * q - 2) / 6

/-- Proposed correction of (10.56)–(10.57): add `(Ω₀ − 1)²/120 + 5 q₀ (Ω₀ − 1)/12`. -/
noncomputable def correctD4y (q j s l Ω : ℝ) : ℝ :=
  printedD4y q j s l Ω + (Ω - 1) ^ 2 / 120 + 5 * q * (Ω - 1) / 12

/-- `y [1 + D¹ y + D² y² + D³ y³ + D⁴ y⁴]`. -/
noncomputable def seriesY4 (q d2 d3 d4 y : ℝ) : ℝ :=
  y * (1 + D1y q * y + d2 * y ^ 2 + d3 * y ^ 3 + d4 * y ^ 4)

/-- Remainder `H₀ d_L − y[1 + D¹y + D²y² + D³y³ + D⁴y⁴]` for curvature `K`, with the
coefficients given as functions of the model's `(q₀, j₀, s₀, l₀, Ω₀)`. -/
noncomputable def remK (D2 : ℝ → ℝ → ℝ → ℝ) (D3 : ℝ → ℝ → ℝ → ℝ → ℝ)
    (D4 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  hubble a t₀ * lumDist K a t₀ t -
    seriesY4 (decel a t₀)
      (D2 (decel a t₀) (cosmoCoeff 3 a t₀) (omega0 K a t₀))
      (D3 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (omega0 K a t₀))
      (D4 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) (omega0 K a t₀))
      (yred a t₀ t)

/-- Claim (10.55), charitable: corrected `D²`, printed `D³`, series to `y³`, remainder `o(y⁴)`,
for every `K` and every analytic, everywhere positive scale factor with `H₀ > 0`. -/
def BambaD3yClaim : Prop :=
  ∀ (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), ContDiff ℝ ω a → (∀ t, 0 < a t) → 0 < hubble a t₀ →
    (fun t => remK correctD2y printedD3y (fun _ _ _ _ _ => 0) K a t₀ t)
      =o[𝓝 t₀] (fun t => yred a t₀ t ^ 4)

/-- Claim (10.56)–(10.57), charitable: corrected `D²`, `D³`, printed `D⁴`, remainder `o(y⁵)`. -/
def BambaD4yClaim : Prop :=
  ∀ (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), ContDiff ℝ ω a → (∀ t, 0 < a t) → 0 < hubble a t₀ →
    (fun t => remK correctD2y correctD3y printedD4y K a t₀ t)
      =o[𝓝 t₀] (fun t => yred a t₀ t ^ 5)

/-- Same claims, past emission only (`t < t₀`). -/
def BambaD3yClaimPast : Prop :=
  ∀ (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), ContDiff ℝ ω a → (∀ t, 0 < a t) → 0 < hubble a t₀ →
    (fun t => remK correctD2y printedD3y (fun _ _ _ _ _ => 0) K a t₀ t)
      =o[𝓝[<] t₀] (fun t => yred a t₀ t ^ 4)

def BambaD4yClaimPast : Prop :=
  ∀ (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), ContDiff ℝ ω a → (∀ t, 0 < a t) → 0 < hubble a t₀ →
    (fun t => remK correctD2y correctD3y printedD4y K a t₀ t)
      =o[𝓝[<] t₀] (fun t => yred a t₀ t ^ 5)

/-- The flat parts of (10.55)–(10.57) are right: at `Ω₀ = 1` the corrections vanish. -/
theorem printed_flat_eq (q j s l : ℝ) :
    printedD3y q j s 1 = correctD3y q j s 1 ∧ printedD4y q j s l 1 = correctD4y q j s l 1 := by
  constructor <;> simp [correctD3y, correctD4y]

/-- **Headline (to prove).** Luminosity distance to fifth order in `y` for every curvature `K`
and every scale factor that is `C⁵` at `t₀` with `a(t₀) ≠ 0`, `H₀ ≠ 0`. -/
theorem lumDist_y_fifth_order (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 5 a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0) :
    (fun t => remK correctD2y correctD3y correctD4y K a t₀ t) =o[𝓝 t₀]
      (fun t => yred a t₀ t ^ 5) := by
  sorry

theorem bambaD3yClaim_false : ¬ BambaD3yClaim := by
  sorry

theorem bambaD4yClaim_false : ¬ BambaD4yClaim := by
  sorry

theorem bambaD3yClaimPast_false : ¬ BambaD3yClaimPast := by
  sorry

theorem bambaD4yClaimPast_false : ¬ BambaD4yClaimPast := by
  sorry

end Work.Cosmography.BambaK
