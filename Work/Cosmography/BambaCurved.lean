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

FROZEN (annex 40.1) in run 2026-10-30T1028Z before proof work (commit b485344).

Referee notes (run 2026-10-30T1028Z, `runs/2026-10-30T1028Z/referee/`): (10.52)–(10.63) are copied
verbatim from Capozziello & Salzano 2009 (arXiv:0902.0088, Eqs. (53)–(64)); identical in 1205.3421
v1–v3. The review's own (10.30) truncates `r₀ = χ − Kχ³/3! + O(χ⁵)`, which explains the
`(Ω₀ − 1)²/120` part of the D⁴ error; the `5q₀(Ω₀ − 1)/12` part and the whole D³ error are not
explained by that truncation (the closed exponential witness fails under either reading). The
correct D³ with curvature agrees with Vitagliano et al. 2010 (arXiv:0911.1249) Eq. (1.9).
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

/-! ### Algebra (polynomials generated by `runs/2026-10-30T1028Z/scripts/gen_curved.py`; Lean checks
every identity) -/

/-- Degree-4 truncation of `1/A`. -/
noncomputable def B4 (q j s l k x : ℝ) : ℝ :=
  j*x^4/3 + j*x^3/6 + q^2*x^4/4 + 3*q*x^4/2 + q*x^3 + q*x^2/2 - s*x^4/24 + x^4 + x^3 + x^2 + x + 1

/-- `A B4 = 1 + x⁵ C5`. -/
noncomputable def C5 (q j s l k x : ℝ) : ℝ :=
  -j^2*x^2/18 - j^2*x/36 - j*l*x^4/360 - j*l*x^3/720 - j*q^2*x^2/24 - j*q*x^2/4 - j*q*x/3 - j*q/6 + j*s*x^3/72 + j*s*x^2/72 - j*x^2/6 - j*x/6 - j/2 - l*q^2*x^4/480 - l*q*x^4/80 - l*q*x^3/120 - l*q*x^2/240 + l*s*x^4/2880 - l*x^4/120 - l*x^3/120 - l*x^2/120 - l*x/120 - l/120 - q^3*x/8 + q^2*s*x^3/96 - 3*q^2*x/4 - 3*q^2/4 + q*s*x^3/16 + q*s*x^2/24 + q*s*x/24 - q*x/2 - 2*q - s^2*x^3/576 + s*x^3/24 + s*x^2/24 + s*x/24 + s/12 - 1

/-- `∫₀ˣ B4`: `a₀ H₀ χ` to fifth order. -/
noncomputable def P5 (q j s l k x : ℝ) : ℝ :=
  j*x^5/15 + j*x^4/24 + q^2*x^5/20 + 3*q*x^5/10 + q*x^4/4 + q*x^3/6 - s*x^5/120 + x^5/5 + x^4/4 + x^3/3 + x^2/2 + x

/-- `P5 = x P5q`. -/
noncomputable def P5q (q j s l k x : ℝ) : ℝ :=
  j*x^4/15 + j*x^3/24 + q^2*x^4/20 + 3*q*x^4/10 + q*x^3/4 + q*x^2/6 - s*x^4/120 + x^4/5 + x^3/4 + x^2/3 + x/2 + 1

/-- Degree-5 truncation of `P5^2`. -/
noncomputable def M2 (q j s l k x : ℝ) : ℝ :=
  j*x^5/12 + 2*q*x^5/3 + q*x^4/3 + 5*x^5/6 + 11*x^4/12 + x^3 + x^2

/-- Product remainder (`… = … + x⁶ ·`). -/
noncomputable def WM2 (q j s l k x : ℝ) : ℝ :=
  j^2*x^4/225 + j^2*x^3/180 + j^2*x^2/576 + j*q^2*x^4/150 + j*q^2*x^3/240 + j*q*x^4/25 + 7*j*q*x^3/120 + 31*j*q*x^2/720 + j*q*x/72 - j*s*x^4/900 - j*s*x^3/1440 + 2*j*x^4/75 + j*x^3/20 + 47*j*x^2/720 + 17*j*x/180 + 7*j/40 + q^4*x^4/400 + 3*q^3*x^4/100 + q^3*x^3/40 + q^3*x^2/60 - q^2*s*x^4/1200 + 11*q^2*x^4/100 + 7*q^2*x^3/40 + 47*q^2*x^2/240 + 2*q^2*x/15 + 23*q^2/180 - q*s*x^4/200 - q*s*x^3/240 - q*s*x^2/360 + 3*q*x^4/25 + q*x^3/4 + 47*q*x^2/120 + 11*q*x/20 + 173*q/180 + s^2*x^4/14400 - s*x^4/300 - s*x^3/240 - s*x^2/180 - s*x/120 - s/60 + x^4/25 + x^3/10 + 47*x^2/240 + 11*x/30 + 137/180

/-- Degree-5 truncation of `P5^3`. -/
noncomputable def M3 (q j s l k x : ℝ) : ℝ :=
  q*x^5/2 + 7*x^5/4 + 3*x^4/2 + x^3

/-- Product remainder (`… = … + x⁶ ·`). -/
noncomputable def WM3 (q j s l k x : ℝ) : ℝ :=
  j^2*x^4/180 + j^2*x^3/288 + j*q^2*x^4/240 + 5*j*q*x^4/72 + 17*j*q*x^3/240 + j*q*x^2/36 - j*s*x^4/1440 + 13*j*x^4/180 + 7*j*x^3/60 + 191*j*x^2/1440 + 3*j*x/20 + j/8 + q^3*x^4/30 + q^3*x^3/60 + 29*q^2*x^4/120 + 5*q^2*x^3/16 + 11*q^2*x^2/45 + 19*q^2*x/180 - q*s*x^4/180 - q*s*x^3/360 + 23*q*x^4/60 + 43*q*x^3/60 + 701*q*x^2/720 + 413*q*x/360 + 5*q/4 - s*x^4/144 - 11*s*x^3/1440 - s*x^2/120 - s*x/120 + x^4/6 + 47*x^3/120 + 509*x^2/720 + 211*x/180 + 15/8

/-- Degree-5 truncation of `P5^4`. -/
noncomputable def M4 (q j s l k x : ℝ) : ℝ :=
  2*x^5 + x^4

/-- Product remainder (`… = … + x⁶ ·`). -/
noncomputable def WM4 (q j s l k x : ℝ) : ℝ :=
  j*q*x^4/30 + j*q*x^3/48 + 7*j*x^4/60 + 83*j*x^3/480 + 31*j*x^2/240 + j*x/24 + q^3*x^4/40 + 19*q^2*x^4/80 + q^2*x^3/5 + 2*q^2*x^2/15 - q*s*x^4/240 + 5*q*x^4/8 + 81*q*x^3/80 + 17*q*x^2/15 + 3*q*x/4 + 2*q/3 - 7*s*x^4/480 - s*x^3/80 - s*x^2/120 + 7*x^4/20 + 59*x^3/80 + 139*x^2/120 + 13*x/8 + 17/6

/-- Degree-5 truncation of `P5^5`. -/
noncomputable def M5 (q j s l k x : ℝ) : ℝ :=
  x^5

/-- Product remainder (`… = … + x⁶ ·`). -/
noncomputable def WM5 (q j s l k x : ℝ) : ℝ :=
  2*j*x^4/15 + 3*j*x^3/20 + j*x^2/24 + q^2*x^4/10 + q^2*x^3/20 + 3*q*x^4/5 + 4*q*x^3/5 + 7*q*x^2/12 + q*x/6 - s*x^4/60 - s*x^3/120 + 2*x^4/5 + 7*x^3/10 + 11*x^2/12 + 4*x/3 + 5/2

/-- Degree-5 truncation of `(1 − A)^2`. -/
noncomputable def N2 (q j s l k x : ℝ) : ℝ :=
  j*q*x^5/6 + j*x^4/3 + q^2*x^4/4 + q*x^3 - s*x^5/12 + x^2

/-- Product remainder (`… = … + x⁶ ·`). -/
noncomputable def WN2 (q j s l k x : ℝ) : ℝ :=
  j^2/36 + j*l*x^2/360 - j*s*x/72 + l^2*x^4/14400 + l*q*x/120 - l*s*x^3/1440 + l/60 - q*s/24 + s^2*x^2/576

/-- Degree-5 truncation of `(1 − A)^3`. -/
noncomputable def N3 (q j s l k x : ℝ) : ℝ :=
  j*x^5/2 + 3*q^2*x^5/4 + 3*q*x^4/2 + x^3

/-- Product remainder (`… = … + x⁶ ·`). -/
noncomputable def WN3 (q j s l k x : ℝ) : ℝ :=
  j^2*q*x^2/36 + j^2*x/18 + j*l*q*x^4/720 + j*l*x^3/360 + j*q^2*x/8 - j*q*s*x^3/144 + j*q/2 - j*s*x^2/36 + l*q^2*x^3/480 + l*q*x^2/120 - l*s*x^4/1440 + l*x/120 + q^3/8 - q^2*s*x^2/96 - q*s*x/12 + s^2*x^3/288 - s/8

/-- Degree-5 truncation of `(1 − A)^4`. -/
noncomputable def N4 (q j s l k x : ℝ) : ℝ :=
  2*q*x^5 + x^4

/-- Product remainder (`… = … + x⁶ ·`). -/
noncomputable def WN4 (q j s l k x : ℝ) : ℝ :=
  j^2*x^2/12 + j*l*x^4/240 + j*q^2*x^2/8 + j*q*x/2 - j*s*x^3/48 + 2*j/3 + l*q^2*x^4/160 + l*q*x^3/80 + l*x^2/120 + 3*q^3*x/8 - q^2*s*x^3/32 + 3*q^2/2 - q*s*x^2/16 - s*x/24

/-- Degree-5 truncation of `(1 − A)^5`. -/
noncomputable def N5 (q j s l k x : ℝ) : ℝ :=
  x^5

/-- Product remainder (`… = … + x⁶ ·`). -/
noncomputable def WN5 (q j s l k x : ℝ) : ℝ :=
  j*q*x^2/3 + j*x/6 + l*q*x^4/60 + l*x^3/120 + q^2*x - q*s*x^3/12 + 5*q/2 - s*x^2/24

/-- `A · Spoly = Fpoly + x⁶ Wf`. -/
noncomputable def Wf (q j s l k x : ℝ) : ℝ :=
  -7*j^2*x^2/80 - 5*j^2*x/144 - j*k^2*x^2/720 + j*k*q*x^2/36 + 17*j*k*x^2/144 + 5*j*k*x/72 + j*k/36 - 7*j*l*x^4/1600 - j*l*x^3/576 - 23*j*q^2*x^2/360 - 173*j*q*x^2/360 - 389*j*q*x/720 - 31*j*q/144 + 7*j*s*x^3/320 + 49*j*s*x^2/2880 - 137*j*x^2/360 - 25*j*x/72 - 299*j/360 - k^2*l*x^4/14400 - k^2*q*x/240 + k^2*s*x^3/2880 - k^2/120 + k*l*q*x^4/720 + 17*k*l*x^4/2880 + k*l*x^3/288 + k*l*x^2/720 + k*q^2*x/12 - k*q*s*x^3/144 + 17*k*q*x/48 + 3*k*q/8 - 17*k*s*x^3/576 - 5*k*s*x^2/288 - k*s*x/144 + 17*k/24 - 23*l*q^2*x^4/7200 - 173*l*q*x^4/7200 - l*q*x^3/72 - l*q*x^2/180 + l*s*x^4/2400 - 137*l*x^4/7200 - 5*l*x^3/288 - 11*l*x^2/720 - l*x/80 - l/120 - 23*q^3*x/120 + 23*q^2*s*x^3/1440 - 173*q^2*x/120 - 73*q^2/60 + 173*q*s*x^3/1440 + 5*q*s*x^2/72 + 19*q*s*x/360 - 137*q*x/120 - 157*q/40 - s^2*x^3/480 + 137*s*x^3/1440 + 25*s*x^2/288 + 11*s*x/144 + 9*s/80 - 137/60

/-- `N1 = 1 − A`. -/
noncomputable def N1 (q j s l k x : ℝ) : ℝ := 1 - CCS.Apoly q j s l x

/-- `F(u) = u − k u³/6 + k² u⁵/120` truncated: `Fpoly = P5 − k M3/6 + k² M5/120`. -/
noncomputable def Fpoly (q j s l k x : ℝ) : ℝ :=
  P5 q j s l k x - k * M3 q j s l k x / 6 + k ^ 2 * M5 q j s l k x / 120

/-- The corrected series in `y`, with `y^n` replaced by its truncation `N_n(x)`. -/
noncomputable def Spoly (q j s l k x : ℝ) : ℝ :=
  N1 q j s l k x + D1y q * N2 q j s l k x + correctD2y q j (1 + k) * N3 q j s l k x
    + correctD3y q j s (1 + k) * N4 q j s l k x + correctD4y q j s l (1 + k) * N5 q j s l k x

lemma idAB (q j s l k x : ℝ) :
    CCS.Apoly q j s l x * B4 q j s l k x = 1 + x ^ 5 * C5 q j s l k x := by
  unfold CCS.Apoly B4 C5; ring
lemma idP (q j s l k x : ℝ) : P5 q j s l k x = x * P5q q j s l k x := by
  unfold P5 P5q; ring
lemma idM2 (q j s l k x : ℝ) :
    P5 q j s l k x * P5 q j s l k x = M2 q j s l k x + x ^ 6 * WM2 q j s l k x := by
  unfold P5 M2 WM2; ring
lemma idM3 (q j s l k x : ℝ) :
    P5 q j s l k x * M2 q j s l k x = M3 q j s l k x + x ^ 6 * WM3 q j s l k x := by
  unfold P5 M2 M3 WM3; ring
lemma idM4 (q j s l k x : ℝ) :
    P5 q j s l k x * M3 q j s l k x = M4 q j s l k x + x ^ 6 * WM4 q j s l k x := by
  unfold P5 M3 M4 WM4; ring
lemma idM5 (q j s l k x : ℝ) :
    P5 q j s l k x * M4 q j s l k x = M5 q j s l k x + x ^ 6 * WM5 q j s l k x := by
  unfold P5 M4 M5 WM5; ring
lemma idN2 (q j s l k x : ℝ) :
    N1 q j s l k x * N1 q j s l k x = N2 q j s l k x + x ^ 6 * WN2 q j s l k x := by
  unfold N1 CCS.Apoly N2 WN2; ring
lemma idN3 (q j s l k x : ℝ) :
    N1 q j s l k x * N2 q j s l k x = N3 q j s l k x + x ^ 6 * WN3 q j s l k x := by
  unfold N1 CCS.Apoly N2 N3 WN3; ring
lemma idN4 (q j s l k x : ℝ) :
    N1 q j s l k x * N3 q j s l k x = N4 q j s l k x + x ^ 6 * WN4 q j s l k x := by
  unfold N1 CCS.Apoly N3 N4 WN4; ring
lemma idN5 (q j s l k x : ℝ) :
    N1 q j s l k x * N4 q j s l k x = N5 q j s l k x + x ^ 6 * WN5 q j s l k x := by
  unfold N1 CCS.Apoly N4 N5 WN5; ring
/-- The coefficient identity: this is where `D¹ … D⁴` (with the curvature corrections) are fixed. -/
lemma idFin (q j s l k x : ℝ) :
    CCS.Apoly q j s l x * Spoly q j s l k x = Fpoly q j s l k x + x ^ 6 * Wf q j s l k x := by
  unfold Spoly Fpoly N1 N2 N3 N4 N5 P5 M3 M5 Wf D1y correctD2y correctD3y correctD4y
    printedD3y printedD4y CCS.Apoly
  ring

lemma hasDerivAt_P5 (q j s l k x : ℝ) : HasDerivAt (P5 q j s l k) (B4 q j s l k x) x := by
  have h := ((((hasDerivAt_id x).add ((hasDerivAt_pow 2 x).div_const 2)).add
    (((hasDerivAt_pow 3 x).const_mul ((q + 2) / 6)))).add
    ((hasDerivAt_pow 4 x).const_mul ((j + 6 * q + 6) / 24))).add
    ((hasDerivAt_pow 5 x).const_mul ((8 * j + 6 * q ^ 2 + 36 * q - s + 24) / 120))
  convert h using 1
  · funext y; simp only [P5, id, Pi.add_apply]; ring
  · simp only [B4, id]; push_cast; ring

lemma cont_B4 (q j s l k : ℝ) : Continuous (B4 q j s l k) := by unfold B4; fun_prop
lemma cont_C5 (q j s l k : ℝ) : Continuous (C5 q j s l k) := by unfold C5; fun_prop
lemma cont_P5 (q j s l k : ℝ) : Continuous (P5 q j s l k) := by unfold P5; fun_prop
lemma cont_P5q (q j s l k : ℝ) : Continuous (P5q q j s l k) := by unfold P5q; fun_prop
lemma cont_M2 (q j s l k : ℝ) : Continuous (M2 q j s l k) := by unfold M2; fun_prop
lemma cont_M3 (q j s l k : ℝ) : Continuous (M3 q j s l k) := by unfold M3; fun_prop
lemma cont_M4 (q j s l k : ℝ) : Continuous (M4 q j s l k) := by unfold M4; fun_prop
lemma cont_WM2 (q j s l k : ℝ) : Continuous (WM2 q j s l k) := by unfold WM2; fun_prop
lemma cont_WM3 (q j s l k : ℝ) : Continuous (WM3 q j s l k) := by unfold WM3; fun_prop
lemma cont_WM4 (q j s l k : ℝ) : Continuous (WM4 q j s l k) := by unfold WM4; fun_prop
lemma cont_WM5 (q j s l k : ℝ) : Continuous (WM5 q j s l k) := by unfold WM5; fun_prop
lemma cont_N1 (q j s l k : ℝ) : Continuous (N1 q j s l k) := by unfold N1 CCS.Apoly; fun_prop
lemma cont_N2 (q j s l k : ℝ) : Continuous (N2 q j s l k) := by unfold N2; fun_prop
lemma cont_N3 (q j s l k : ℝ) : Continuous (N3 q j s l k) := by unfold N3; fun_prop
lemma cont_N4 (q j s l k : ℝ) : Continuous (N4 q j s l k) := by unfold N4; fun_prop
lemma cont_WN2 (q j s l k : ℝ) : Continuous (WN2 q j s l k) := by unfold WN2; fun_prop
lemma cont_WN3 (q j s l k : ℝ) : Continuous (WN3 q j s l k) := by unfold WN3; fun_prop
lemma cont_WN4 (q j s l k : ℝ) : Continuous (WN4 q j s l k) := by unfold WN4; fun_prop
lemma cont_WN5 (q j s l k : ℝ) : Continuous (WN5 q j s l k) := by unfold WN5; fun_prop
lemma cont_A (q j s l : ℝ) : Continuous (CCS.Apoly q j s l) := by unfold CCS.Apoly; fun_prop
lemma cont_Spoly (q j s l k : ℝ) : Continuous (Spoly q j s l k) := by
  unfold Spoly N1 N2 N3 N4 N5 CCS.Apoly; fun_prop
lemma cont_Wf (q j s l k : ℝ) : Continuous (Wf q j s l k) := by unfold Wf; fun_prop

/-! ### Truncated-series arithmetic (no cosmology): `f ≈ p` means `f − p(X) = o(X⁵)` -/

section approx

variable {α : Type*} {L : Filter α} {X : α → ℝ}

lemma approx_bdd (hX : Tendsto X L (𝓝 0)) {f : α → ℝ} {p : ℝ → ℝ} (hp : Continuous p)
    (h : (fun t => f t - p (X t)) =o[L] fun t => X t ^ 5) : f =O[L] fun _ => (1 : ℝ) := by
  have h0 : Tendsto (fun t => f t - p (X t)) L (𝓝 0) :=
    h.trans_tendsto (by simpa using hX.pow 5)
  have h1 := h0.add ((hp.tendsto 0).comp hX)
  simp only [zero_add, Function.comp_def, sub_add_cancel] at h1
  exact h1.isBigO_one ℝ

lemma approx_mul (hX : Tendsto X L (𝓝 0)) {f g : α → ℝ} {p r m W : ℝ → ℝ}
    (hp : Continuous p) (hr : Continuous r) (hW : Continuous W)
    (hid : ∀ x, p x * r x = m x + x ^ 6 * W x)
    (hf : (fun t => f t - p (X t)) =o[L] fun t => X t ^ 5)
    (hg : (fun t => g t - r (X t)) =o[L] fun t => X t ^ 5) :
    (fun t => f t * g t - m (X t)) =o[L] fun t => X t ^ 5 := by
  have b1 : (fun t => (f t - p (X t)) * g t) =o[L] fun t => X t ^ 5 := by
    simpa using hf.mul_isBigO (approx_bdd hX hr hg)
  have b2 : (fun t => p (X t) * (g t - r (X t))) =o[L] fun t => X t ^ 5 := by
    simpa using (CCS.bdd hX p hp).mul_isLittleO hg
  have b3 := CCS.x6 hX _ (CCS.bdd hX _ hW)
  refine ((b1.add b2).add b3).congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
  have := hid (X t)
  simp only
  linear_combination (-1 : ℝ) * this

lemma approx_pow (hX : Tendsto X L (𝓝 0)) {f : α → ℝ} {p r m W : ℝ → ℝ} {n : ℕ}
    (hp : Continuous p) (hr : Continuous r) (hW : Continuous W)
    (hid : ∀ x, p x * r x = m x + x ^ 6 * W x)
    (hf : (fun t => f t - p (X t)) =o[L] fun t => X t ^ 5)
    (hn : (fun t => f t ^ n - r (X t)) =o[L] fun t => X t ^ 5) :
    (fun t => f t ^ (n + 1) - m (X t)) =o[L] fun t => X t ^ 5 := by
  refine (approx_mul hX hp hr hW hid hf hn).congr' (Eventually.of_forall fun t => ?_)
    EventuallyEq.rfl
  simp only [pow_succ']

end approx

/-- `y` has derivative `−H₀` at `t₀` and vanishes there, so `t − t₀ = O(y)`. -/
lemma sub_isBigO_yred (a : ℝ → ℝ) (t₀ : ℝ) (hd : DifferentiableAt ℝ a t₀) (ha0 : a t₀ ≠ 0)
    (hH : hubble a t₀ ≠ 0) : (fun t => t - t₀) =O[𝓝 t₀] fun t => yred a t₀ t := by
  have hy0 : yred a t₀ t₀ = 0 := by
    simp only [yred, redshift, div_self ha0, sub_self, zero_div]
  exact sub_isBigO_of_hasDerivAt (hasDerivAt_yred a t₀ hd ha0) hy0 (neg_ne_zero.2 hH)

lemma alg5 (H B A E x C : ℝ) (hw : A + E ≠ 0) (hab : A * B = 1 + x ^ 5 * C) :
    H * (B - (A + E)⁻¹) = H * ((x ^ 5 * C + E * B) * (A + E)⁻¹) := by
  field_simp
  linear_combination H * hab

/-- **Headline.** Luminosity distance to fifth order in `y` for every curvature `K`
and every scale factor that is `C⁵` at `t₀` with `a(t₀) ≠ 0`, `H₀ ≠ 0`. -/
theorem lumDist_y_fifth_order (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 5 a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0) :
    (fun t => remK correctD2y correctD3y correctD4y K a t₀ t) =o[𝓝 t₀]
      (fun t => yred a t₀ t ^ 5) := by
  set a₀ := a t₀ with ha₀
  set H := hubble a t₀ with hHdef
  set q := decel a t₀ with hq
  set j := cosmoCoeff 3 a t₀ with hj
  set s := cosmoCoeff 4 a t₀ with hs
  set l := cosmoCoeff 5 a t₀ with hl
  set k := K / (a₀ * H) ^ 2 with hk
  have hΩ : omega0 K a t₀ = 1 + k := by
    show 1 + K / (H ^ 2 * a₀ ^ 2) = 1 + K / (a₀ * H) ^ 2
    ring
  have hd : DifferentiableAt ℝ a t₀ := ha.differentiableAt (by norm_num)
  -- a ball on which `a` is `C⁵` and nonzero
  obtain ⟨U, hU, hcd⟩ := ha.contDiffOn le_rfl (by simp)
  have hne : {t | a t ≠ 0} ∈ 𝓝 t₀ := hd.continuousAt.eventually_ne ha0
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hU hne)
  set Bl := Metric.ball t₀ δ with hBl
  have hopen : IsOpen Bl := Metric.isOpen_ball
  have hmem : t₀ ∈ Bl := Metric.mem_ball_self hδ
  have hBl_nhds : Bl ∈ 𝓝 t₀ := hopen.mem_nhds hmem
  have hcdB : ContDiffOn ℝ 5 a Bl := hcd.mono fun t ht => (hball ht).1
  have hnz : ∀ t ∈ Bl, a t ≠ 0 := fun t ht => (hball ht).2
  have hcont : ContinuousOn a Bl := hcdB.continuousOn
  -- Taylor's theorem
  have hT := taylor_isLittleO (convex_ball t₀ δ) hmem hcdB
  rw [hopen.nhdsWithin_eq hmem] at hT
  have hid : ∀ n, iteratedDerivWithin n a Bl t₀ = iteratedDeriv n a t₀ :=
    fun n => iteratedDerivWithin_of_isOpen hopen hmem
  have d1 : iteratedDeriv 1 a t₀ = H * a₀ := by
    rw [iteratedDeriv_one]; simp only [hHdef, hubble]; rw [← ha₀]; field_simp
  have hd1 : deriv a t₀ ≠ 0 := by
    intro h0; apply hH; rw [hHdef]; simp [hubble, h0]
  have d2 : iteratedDeriv 2 a t₀ = -q * H ^ 2 * a₀ := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    simp only [hq, decel, hHdef, hubble]; rw [← ha₀]; field_simp
  have dk : ∀ n, iteratedDeriv n a t₀ = cosmoCoeff n a t₀ * (a₀ * H ^ n) := by
    intro n; simp only [cosmoCoeff, hHdef]
    rw [div_mul_cancel₀]; exact mul_ne_zero ha0 (pow_ne_zero _ hH)
  have hpoly : ∀ t, taylorWithinEval a 5 Bl t₀ t = a₀ * CCS.Apoly q j s l (H * (t₀ - t)) := by
    intro t
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hid, smul_eq_mul]
    rw [iteratedDeriv_zero, d1, d2, dk 3, dk 4, dk 5]
    simp only [CCS.Apoly, Nat.factorial, Nat.cast_ofNat]
    push_cast
    ring
  set X : ℝ → ℝ := fun t => H * (t₀ - t) with hX
  set E : ℝ → ℝ := fun t => a t / a₀ - CCS.Apoly q j s l (X t) with hE
  have hXc : Continuous X := by fun_prop
  have hXt : Tendsto X (𝓝 t₀) (𝓝 0) := by simpa [hX] using hXc.tendsto t₀
  have htX : ∀ n : ℕ, (fun t => (t - t₀) ^ n) =O[𝓝 t₀] fun t => X t ^ n := by
    intro n
    have : (fun t => t - t₀) =O[𝓝 t₀] X := by
      refine IsBigO.of_bound (‖H‖⁻¹) (Eventually.of_forall fun t => ?_)
      simp only [hX, norm_mul]
      rw [← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.2 hH), one_mul, ← norm_neg]; ring_nf; rfl
    exact this.pow n
  have hXt' : ∀ n : ℕ, (fun t => X t ^ n) =O[𝓝 t₀] fun t => (t - t₀) ^ n := by
    intro n
    have : X =O[𝓝 t₀] (fun t => t - t₀) := by
      refine IsBigO.of_bound (‖H‖) (Eventually.of_forall fun t => ?_)
      simp only [hX, norm_mul, ← norm_neg (t₀ - t)]; ring_nf; rfl
    exact this.pow n
  have hEo : E =o[𝓝 t₀] fun t => X t ^ 5 := by
    have h1 : E = fun t => a₀⁻¹ * (a t - taylorWithinEval a 5 Bl t₀ t) := by
      funext t; simp only [hE, hpoly, hX]; field_simp
    rw [h1]
    exact (hT.const_mul_left a₀⁻¹).trans_isBigO (htX 5)
  have hE0 : Tendsto E (𝓝 t₀) (𝓝 0) := by
    have : Tendsto (fun t => X t ^ 5) (𝓝 t₀) (𝓝 0) := by simpa using hXt.pow 5
    exact hEo.trans_tendsto this
  have hwE : ∀ t, a t / a₀ = CCS.Apoly q j s l (X t) + E t := fun t => by simp only [hE]; ring
  have hw1A : Tendsto (fun t => CCS.Apoly q j s l (X t) + E t) (𝓝 t₀) (𝓝 1) := by
    have h := (((cont_A q j s l).tendsto 0).comp hXt).add hE0
    rw [show CCS.Apoly q j s l 0 + 0 = 1 by simp [CCS.Apoly]] at h
    exact h
  have hwinvA : (fun t => (CCS.Apoly q j s l (X t) + E t)⁻¹) =O[𝓝 t₀] (fun _ => (1 : ℝ)) :=
    (hw1A.inv₀ one_ne_zero).isBigO_one ℝ
  have hw1 : Tendsto (fun t => a t / a₀) (𝓝 t₀) (𝓝 1) := hw1A.congr fun t => (hwE t).symm
  have hwinv : (fun t => (a t / a₀)⁻¹) =O[𝓝 t₀] (fun _ => (1 : ℝ)) :=
    (hw1.inv₀ one_ne_zero).isBigO_one ℝ
  -- comoving distance: u = a₀ H χ = P5(X) + o(X⁵)
  set u : ℝ → ℝ := fun t => a₀ * H * comoving a t₀ t with hu
  set R : ℝ → ℝ := fun t => u t - P5 q j s l k (X t) with hR
  set R' : ℝ → ℝ := fun t => H * (B4 q j s l k (X t) - a₀ / a t) with hR'
  have hfc : ContinuousOn (fun s => 1 / a s) Bl := continuousOn_const.div hcont hnz
  have hderR : ∀ t ∈ Bl, HasDerivAt R (R' t) t := by
    intro t ht
    have hsub : Set.uIcc t t₀ ⊆ Bl := (convex_ball t₀ δ).ordConnected.uIcc_subset ht hmem
    have hχ : HasDerivAt (comoving a t₀) (-(1 / a t)) t :=
      intervalIntegral.integral_hasDerivAt_left ((hfc.mono hsub).intervalIntegrable)
        (hfc.stronglyMeasurableAtFilter hopen t ht) (hfc.continuousAt (hopen.mem_nhds ht))
    have hXd : HasDerivAt X (-H) t := by
      simpa using ((hasDerivAt_id t).const_sub t₀).const_mul H
    have hP := (hasDerivAt_P5 q j s l k (X t)).comp t hXd
    have := (hχ.const_mul (a₀ * H)).sub hP
    have e : R' t = a₀ * H * -(1 / a t) - B4 q j s l k (X t) * -H := by
      show H * (B4 q j s l k (X t) - a₀ / a t) = _
      ring
    rw [e]; exact this
  have hR0 : R t₀ = 0 := by simp [hR, hu, comoving, hX, P5]
  have hR'o : R' =o[𝓝 t₀] fun t => (t - t₀) ^ 4 := by
    have e1 : ∀ t ∈ Bl, R' t = H * ((X t ^ 5 * C5 q j s l k (X t) + E t * B4 q j s l k (X t))
        * (CCS.Apoly q j s l (X t) + E t)⁻¹) := by
      intro t ht
      have hw : CCS.Apoly q j s l (X t) + E t ≠ 0 := by
        rw [← hwE]; exact div_ne_zero (hnz t ht) ha0
      have ha' : a₀ / a t = (CCS.Apoly q j s l (X t) + E t)⁻¹ := by rw [← hwE, inv_div]
      show H * (B4 q j s l k (X t) - a₀ / a t) = _
      rw [ha']
      exact alg5 H _ _ _ _ _ hw (idAB q j s l k (X t))
    have b1 : (fun t => X t ^ 5 * C5 q j s l k (X t)) =o[𝓝 t₀] fun t => X t ^ 4 :=
      pow_succ_mul_isLittleO hXt 4 _ (CCS.bdd hXt _ (cont_C5 q j s l k))
    have hX54 : (fun t => X t ^ 5) =o[𝓝 t₀] fun t => X t ^ 4 := by
      simpa using pow_succ_mul_isLittleO hXt 4 (fun _ => (1 : ℝ)) (isBigO_refl _ _)
    have b2 : (fun t => E t * B4 q j s l k (X t)) =o[𝓝 t₀] fun t => X t ^ 4 := by
      simpa using (hEo.trans hX54).mul_isBigO (CCS.bdd hXt _ (cont_B4 q j s l k))
    have b3 := (((b1.add b2).mul_isBigO hwinvA).const_mul_left H)
    simp only [mul_one] at b3
    exact (b3.congr' (Filter.eventually_of_mem hBl_nhds fun t ht => (e1 t ht).symm)
      EventuallyEq.rfl).trans_isBigO (hXt' 4)
  have hRo : R =o[𝓝 t₀] fun t => X t ^ 5 :=
    (littleO_of_hasDerivAt hR0 (Filter.eventually_of_mem hBl_nhds hderR) hR'o).trans_isBigO
      (htX 5)
  have au0 : (fun t => u t - P5 q j s l k (X t)) =o[𝓝 t₀] fun t => X t ^ 5 := hRo
  have au1 : (fun t => u t ^ 1 - P5 q j s l k (X t)) =o[𝓝 t₀] fun t => X t ^ 5 := by
    simpa only [pow_one] using au0
  have au2 := approx_pow (n := 1) hXt (cont_P5 q j s l k) (cont_P5 q j s l k)
    (cont_WM2 q j s l k) (idM2 q j s l k) au0 au1
  have au3 := approx_pow (n := 2) hXt (cont_P5 q j s l k) (cont_M2 q j s l k)
    (cont_WM3 q j s l k) (idM3 q j s l k) au0 au2
  have au4 := approx_pow (n := 3) hXt (cont_P5 q j s l k) (cont_M3 q j s l k)
    (cont_WM4 q j s l k) (idM4 q j s l k) au0 au3
  have au5 := approx_pow (n := 4) hXt (cont_P5 q j s l k) (cont_M4 q j s l k)
    (cont_WM5 q j s l k) (idM5 q j s l k) au0 au4
  -- χ = O(X), so the transverse expansion transfers
  have hX5X : (fun t => X t ^ 5) =O[𝓝 t₀] X := by
    have h := (isBigO_refl X (𝓝 t₀)).mul ((hXt.pow 4).isBigO_one ℝ)
    refine h.congr' (Eventually.of_forall fun t => ?_) (Eventually.of_forall fun t => ?_)
    · simp only; ring
    · simp
  have huX : u =O[𝓝 t₀] X := by
    have h1 : (fun t => P5 q j s l k (X t)) =O[𝓝 t₀] X := by
      have := (isBigO_refl X (𝓝 t₀)).mul (CCS.bdd hXt _ (cont_P5q q j s l k))
      refine this.congr' (Eventually.of_forall fun t => ?_) (Eventually.of_forall fun t => ?_)
      · simp only [idP]
      · simp
    have h2 : R =O[𝓝 t₀] X := hRo.isBigO.trans hX5X
    refine (h2.add h1).congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
    simp only [hR]; ring
  have haH : a₀ * H ≠ 0 := mul_ne_zero ha0 hH
  have hχX : (fun t => comoving a t₀ t) =O[𝓝 t₀] X := by
    have := huX.const_mul_left (a₀ * H)⁻¹
    refine this.congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
    simp only [hu]; field_simp
  have hχ0 : Tendsto (fun t => comoving a t₀ t) (𝓝 t₀) (𝓝 0) := hχX.trans_tendsto hXt
  have hS := ((transverse_expansion K).comp_tendsto hχ0).const_mul_left (a₀ * H)
  have hS' := hS.trans_isBigO (hχX.pow 5)
  have aSig : (fun t => a₀ * H * transverse K (comoving a t₀ t) - Fpoly q j s l k (X t))
      =o[𝓝 t₀] fun t => X t ^ 5 := by
    have h := ((hS'.add au0).sub (au3.const_mul_left (k / 6))).add
      (au5.const_mul_left (k ^ 2 / 120))
    refine h.congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
    simp only [Function.comp, hu, Fpoly, hk]
    field_simp
    ring
  -- y = 1 − a/a₀ ≈ N1(X), and its powers
  have hyE : ∀ t ∈ Bl, yred a t₀ t = 1 - a t / a₀ := fun t ht => by
    have := hnz t ht
    simp only [yred, redshift, ← ha₀]
    field_simp
    linear_combination (a₀ - a t) * mul_inv_cancel₀ ha0
  have ay1 : (fun t => yred a t₀ t - N1 q j s l k (X t)) =o[𝓝 t₀] fun t => X t ^ 5 := by
    refine hEo.neg_left.congr' (Filter.eventually_of_mem hBl_nhds fun t ht => ?_)
      EventuallyEq.rfl
    show -E t = yred a t₀ t - N1 q j s l k (X t)
    rw [hyE t ht]; simp only [hE, N1]; ring
  have ay1' : (fun t => yred a t₀ t ^ 1 - N1 q j s l k (X t)) =o[𝓝 t₀] fun t => X t ^ 5 := by
    simpa only [pow_one] using ay1
  have ay2 := approx_pow (n := 1) hXt (cont_N1 q j s l k) (cont_N1 q j s l k)
    (cont_WN2 q j s l k) (idN2 q j s l k) ay1 ay1'
  have ay3 := approx_pow (n := 2) hXt (cont_N1 q j s l k) (cont_N2 q j s l k)
    (cont_WN3 q j s l k) (idN3 q j s l k) ay1 ay2
  have ay4 := approx_pow (n := 3) hXt (cont_N1 q j s l k) (cont_N3 q j s l k)
    (cont_WN4 q j s l k) (idN4 q j s l k) ay1 ay3
  have ay5 := approx_pow (n := 4) hXt (cont_N1 q j s l k) (cont_N4 q j s l k)
    (cont_WN5 q j s l k) (idN5 q j s l k) ay1 ay4
  have aS : (fun t => seriesY4 q (correctD2y q j (1 + k)) (correctD3y q j s (1 + k))
      (correctD4y q j s l (1 + k)) (yred a t₀ t) - Spoly q j s l k (X t))
      =o[𝓝 t₀] fun t => X t ^ 5 := by
    have h := ((((ay1.add (ay2.const_mul_left (D1y q))).add
      (ay3.const_mul_left (correctD2y q j (1 + k)))).add
      (ay4.const_mul_left (correctD3y q j s (1 + k)))).add
      (ay5.const_mul_left (correctD4y q j s l (1 + k))))
    refine h.congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
    simp only [seriesY4, Spoly]; ring
  have aw : (fun t => a t / a₀ - CCS.Apoly q j s l (X t)) =o[𝓝 t₀] fun t => X t ^ 5 := hEo
  have awS := approx_mul hXt (cont_A q j s l) (cont_Spoly q j s l k) (cont_Wf q j s l k)
    (idFin q j s l k) aw aS
  have hN := (aSig.sub awS).mul_isBigO hwinv
  simp only [mul_one] at hN
  have e2 : ∀ t ∈ Bl, remK correctD2y correctD3y correctD4y K a t₀ t =
      ((a₀ * H * transverse K (comoving a t₀ t) - Fpoly q j s l k (X t)) -
        (a t / a₀ * seriesY4 q (correctD2y q j (1 + k)) (correctD3y q j s (1 + k))
          (correctD4y q j s l (1 + k)) (yred a t₀ t) - Fpoly q j s l k (X t)))
        * (a t / a₀)⁻¹ := by
    intro t ht
    have := hnz t ht
    show H * (a₀ * (1 + (a₀ / a t - 1)) * transverse K (comoving a t₀ t)) -
      seriesY4 q (correctD2y q j (omega0 K a t₀)) (correctD3y q j s (omega0 K a t₀))
        (correctD4y q j s l (omega0 K a t₀)) (yred a t₀ t) = _
    rw [hΩ]
    field_simp
    ring
  have hfin := hN.congr' (Filter.eventually_of_mem hBl_nhds fun t ht => (e2 t ht).symm)
    EventuallyEq.rfl
  have hXy : X =O[𝓝 t₀] fun t => yred a t₀ t := by
    have : X =O[𝓝 t₀] (fun t => t - t₀) := by simpa using hXt' 1
    exact this.trans (sub_isBigO_yred a t₀ hd ha0 hH)
  exact hfin.trans_isBigO (hXy.pow 5)

/-- `yⁿ` is not `o(yⁿ)` from the past. -/
lemma not_isLittleO_self_past (a : ℝ → ℝ) (t₀ : ℝ) (hd : DifferentiableAt ℝ a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0) (n : ℕ) {c : ℝ} (hc : c ≠ 0)
    (h : (fun t => c * yred a t₀ t ^ n) =o[𝓝[<] t₀] (fun t => yred a t₀ t ^ n)) : False := by
  have hself : (fun t => yred a t₀ t ^ n) =o[𝓝[<] t₀] (fun t => yred a t₀ t ^ n) :=
    (h.const_mul_left c⁻¹).congr' (Eventually.of_forall fun t => by
      simp only; rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]) EventuallyEq.rfl
  have hev := (hasDerivAt_yred a t₀ hd ha0).eventually_ne (c := 0) (neg_ne_zero.2 hH)
  have hev' : ∀ᶠ t in 𝓝[<] t₀, yred a t₀ t ≠ 0 :=
    nhdsWithin_mono t₀ (fun t (ht : t < t₀) => ne_of_lt ht) hev
  have hfreq : ∃ᶠ t in 𝓝[<] t₀, ‖yred a t₀ t ^ n‖ ≠ 0 :=
    (hev'.mono fun t ht => by simp [ht]).frequently
  exact isLittleO_irrefl' hfreq hself

lemma yred_tendsto_past (a : ℝ → ℝ) (t₀ : ℝ) (hd : DifferentiableAt ℝ a t₀) (ha0 : a t₀ ≠ 0) :
    Tendsto (fun t => yred a t₀ t) (𝓝[<] t₀) (𝓝 0) := by
  have h := (hasDerivAt_yred a t₀ hd ha0).continuousAt.tendsto
  have hy0 : yred a t₀ t₀ = 0 := by
    simp only [yred, redshift, div_self ha0, sub_self, zero_div]
  rw [hy0] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- The printed `D³_{L,y}` (with the corrected `D²`) fails, from the past, in every `C⁵` model
with `a(t₀) ≠ 0`, `H₀ ≠ 0`, `Ω₀ ≠ 1` and `q₀ ≠ 2/3`. -/
theorem printedD3y_fails_past (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 5 a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0)
    (hD : (omega0 K a t₀ - 1) * (3 * decel a t₀ - 2) ≠ 0) :
    ¬ (fun t => remK correctD2y printedD3y (fun _ _ _ _ _ => 0) K a t₀ t)
      =o[𝓝[<] t₀] (fun t => yred a t₀ t ^ 4) := by
  intro hp
  have hd : DifferentiableAt ℝ a t₀ := ha.differentiableAt (by norm_num)
  have hy0 := yred_tendsto_past a t₀ hd ha0
  have h54 : (fun t => yred a t₀ t ^ 5) =o[𝓝[<] t₀] (fun t => yred a t₀ t ^ 4) := by
    simpa using pow_succ_mul_isLittleO hy0 4 (fun _ => (1 : ℝ)) (isBigO_refl _ _)
  have hc := ((lumDist_y_fifth_order K a t₀ ha ha0 hH).mono
    (nhdsWithin_le_nhds (s := Set.Iio t₀))).trans h54
  have hd4 := h54.const_mul_left (correctD4y (decel a t₀) (cosmoCoeff 3 a t₀)
    (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) (omega0 K a t₀))
  set c : ℝ := (omega0 K a t₀ - 1) * (3 * decel a t₀ - 2) / 6 with hcdef
  have hc0 : c ≠ 0 := div_ne_zero hD (by norm_num)
  have hdiff : (fun t => c * yred a t₀ t ^ 4) =o[𝓝[<] t₀] (fun t => yred a t₀ t ^ 4) := by
    refine ((hp.sub hc).sub hd4).congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
    simp only [remK, seriesY4, correctD3y, hcdef]; ring
  exact not_isLittleO_self_past a t₀ hd ha0 hH 4 hc0 hdiff

/-- Two-sided version. -/
theorem printedD3y_fails (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 5 a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0)
    (hD : (omega0 K a t₀ - 1) * (3 * decel a t₀ - 2) ≠ 0) :
    ¬ (fun t => remK correctD2y printedD3y (fun _ _ _ _ _ => 0) K a t₀ t)
      =o[𝓝 t₀] (fun t => yred a t₀ t ^ 4) :=
  fun hp => printedD3y_fails_past K a t₀ ha ha0 hH hD
    (hp.mono (nhdsWithin_le_nhds (s := Set.Iio t₀)))

/-- The printed `D⁴_{L,y}` (with corrected `D²`, `D³`) fails, from the past, in every `C⁵` model
with `a(t₀) ≠ 0`, `H₀ ≠ 0` and `(Ω₀ − 1)²/120 + 5 q₀ (Ω₀ − 1)/12 ≠ 0`. -/
theorem printedD4y_fails_past (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 5 a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0)
    (hD : (omega0 K a t₀ - 1) ^ 2 / 120 + 5 * decel a t₀ * (omega0 K a t₀ - 1) / 12 ≠ 0) :
    ¬ (fun t => remK correctD2y correctD3y printedD4y K a t₀ t)
      =o[𝓝[<] t₀] (fun t => yred a t₀ t ^ 5) := by
  intro hp
  have hd : DifferentiableAt ℝ a t₀ := ha.differentiableAt (by norm_num)
  have hc := (lumDist_y_fifth_order K a t₀ ha ha0 hH).mono (nhdsWithin_le_nhds (s := Set.Iio t₀))
  set c : ℝ := (omega0 K a t₀ - 1) ^ 2 / 120 + 5 * decel a t₀ * (omega0 K a t₀ - 1) / 12
    with hcdef
  have hdiff : (fun t => c * yred a t₀ t ^ 5) =o[𝓝[<] t₀] (fun t => yred a t₀ t ^ 5) := by
    refine (hp.sub hc).congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
    simp only [remK, seriesY4, correctD4y, hcdef]; ring
  exact not_isLittleO_self_past a t₀ hd ha0 hH 5 hD hdiff

/-- Two-sided version. -/
theorem printedD4y_fails (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 5 a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0)
    (hD : (omega0 K a t₀ - 1) ^ 2 / 120 + 5 * decel a t₀ * (omega0 K a t₀ - 1) / 12 ≠ 0) :
    ¬ (fun t => remK correctD2y correctD3y printedD4y K a t₀ t)
      =o[𝓝 t₀] (fun t => yred a t₀ t ^ 5) :=
  fun hp => printedD4y_fails_past K a t₀ ha ha0 hH hD
    (hp.mono (nhdsWithin_le_nhds (s := Set.Iio t₀)))

/-- Closed exponential expansion: `a = exp` at `t₀ = 0` with closed spatial sections `K = 1`
(an FLRW metric; not de Sitter spacetime, whose closed slicing is `a = cosh t`):
`H₀ = 1`, `q₀ = −1`, `Ω₀ = 2`. -/
lemma closedExp_vals : hubble Real.exp 0 = 1 ∧ decel Real.exp 0 = -1 ∧ omega0 1 Real.exp 0 = 2 := by
  have hH : hubble Real.exp 0 = 1 := by simp [hubble, Real.deriv_exp]
  refine ⟨hH, by simp [decel, Real.deriv_exp], ?_⟩
  simp only [omega0, hH]; norm_num

theorem bambaD3yClaim_false : ¬ BambaD3yClaim := by
  intro h
  obtain ⟨hH, hq, hΩ⟩ := closedExp_vals
  exact printedD3y_fails 1 Real.exp 0 Real.contDiff_exp.contDiffAt (Real.exp_pos 0).ne'
    (by rw [hH]; norm_num) (by rw [hq, hΩ]; norm_num)
    (h 1 Real.exp 0 Real.contDiff_exp Real.exp_pos (by rw [hH]; norm_num))

theorem bambaD4yClaim_false : ¬ BambaD4yClaim := by
  intro h
  obtain ⟨hH, hq, hΩ⟩ := closedExp_vals
  exact printedD4y_fails 1 Real.exp 0 Real.contDiff_exp.contDiffAt (Real.exp_pos 0).ne'
    (by rw [hH]; norm_num) (by rw [hq, hΩ]; norm_num)
    (h 1 Real.exp 0 Real.contDiff_exp Real.exp_pos (by rw [hH]; norm_num))

theorem bambaD3yClaimPast_false : ¬ BambaD3yClaimPast := by
  intro h
  obtain ⟨hH, hq, hΩ⟩ := closedExp_vals
  exact printedD3y_fails_past 1 Real.exp 0 Real.contDiff_exp.contDiffAt (Real.exp_pos 0).ne'
    (by rw [hH]; norm_num) (by rw [hq, hΩ]; norm_num)
    (h 1 Real.exp 0 Real.contDiff_exp Real.exp_pos (by rw [hH]; norm_num))

theorem bambaD4yClaimPast_false : ¬ BambaD4yClaimPast := by
  intro h
  obtain ⟨hH, hq, hΩ⟩ := closedExp_vals
  exact printedD4y_fails_past 1 Real.exp 0 Real.contDiff_exp.contDiffAt (Real.exp_pos 0).ne'
    (by rw [hH]; norm_num) (by rw [hq, hΩ]; norm_num)
    (h 1 Real.exp 0 Real.contDiff_exp Real.exp_pos (by rw [hH]; norm_num))

/-- Milne universe (`a(t) = t`, `K = −1`, observed at `t₀ = 1`; empty open FLRW, exact
`H₀ d_L = z + z²/2`): `H₀ = 1`, `q₀ = 0`, `Ω₀ = 0`. -/
lemma milne_vals : hubble (fun t => t) 1 = 1 ∧ decel (fun t => t) 1 = 0 ∧
    omega0 (-1) (fun t => t) 1 = 0 := by
  have hH : hubble (fun t => t) 1 = 1 := by simp [hubble]
  refine ⟨hH, by simp [decel], ?_⟩
  simp only [omega0, hH]; norm_num

/-- Both printed curvature terms fail in the Milne universe, from the past. Standalone instance
refutations: `a = t` is not positive for all `t`, so Milne is not an instance of the frozen claims
(which the closed exponential model refutes). The Milne `D⁴` failure comes entirely from the
`(Ω₀ − 1)²/120` term (`q₀ = 0`), i.e. from the `K²χ⁵/120` term the review truncates in (10.30). -/
theorem milne_printedD3y_fails_past :
    ¬ (fun t => remK correctD2y printedD3y (fun _ _ _ _ _ => 0) (-1) (fun t => t) 1 t)
      =o[𝓝[<] 1] (fun t => yred (fun t => t) 1 t ^ 4) := by
  obtain ⟨hH, hq, hΩ⟩ := milne_vals
  exact printedD3y_fails_past (-1) (fun t => t) 1 contDiffAt_id one_ne_zero
    (by rw [hH]; norm_num) (by rw [hq, hΩ]; norm_num)

theorem milne_printedD4y_fails_past :
    ¬ (fun t => remK correctD2y correctD3y printedD4y (-1) (fun t => t) 1 t)
      =o[𝓝[<] 1] (fun t => yred (fun t => t) 1 t ^ 5) := by
  obtain ⟨hH, hq, hΩ⟩ := milne_vals
  exact printedD4y_fails_past (-1) (fun t => t) 1 contDiffAt_id one_ne_zero
    (by rw [hH]; norm_num) (by rw [hq, hΩ]; norm_num)

end Work.Cosmography.BambaK
