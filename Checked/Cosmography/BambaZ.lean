import Checked.Cosmography.BambaAngular

/-!
# Candidate C9: Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012),
arXiv:1205.3421v3, Sec. X, Eqs. (10.38)–(10.51): z-redshift series of `d_L` and `d_A` with
spatial curvature

Source (typeset, v1–v3 identical by pdftotext of the equation block; crops
`runs/2026-10-30T1232Z/typeset/review_v3_p110_eq10.38-44_z_dL.png`, `..._eq10.46-51_z_dA.png`):
"d_L(z) = (cz/H₀){D⁰_L + D¹_L z + D²_L z² + D³_L z³ + D⁴_L z⁴ + O(z⁵)} (10.38),
D⁰_L = 1, D¹_L = −½(−1 + q₀), D²_L = −⅙(1 − q₀ − 3q₀² + j₀ + Kc²/(H₀²a₀²)),
D³_L = (1/24)[2 − 2q₀ − 15q₀² − 15q₀³ + 5j₀ + 10q₀j₀ + s₀ + 2Kc²(1 + 3q₀)/(H₀²a₀²)],
D⁴_L = (1/120)[−6 + 6q₀ + 81q₀² + 165q₀³ + 105q₀⁴ − 110q₀j₀ − 105q₀²j₀ − 15q₀s₀ +
− 27j₀ + 10j² − 11s₀ − l₀ − 5Kc²(1 + 8q₀ + 9q₀² − 2j₀)/(a₀²H₀²)] (10.43)–(10.44);
d_A(z) = (cz/H₀){D⁰_A + … + D⁴_A z⁴ + O(z⁵)} (10.45), D⁰_A = 1, D¹_A = −½(3 + q₀),
D²_A = ⅙[11 + 7q₀ + 3q₀² − j₀ − Kc²/(H₀²a₀²)],
D³_A = −(1/24)[50 + 46q₀ + 39q₀² + 15q₀³ − 13j₀ − 10q₀j₀ − s₀ − 2Kc²(5 + 3q₀)/(H₀²a₀²)],
D⁴_A = (1/120)[274 + 326q₀ + 411q₀² + 315q₀³ + 105q₀⁴ − 210q₀j₀ − 105q₀²j₀ − 15q₀s₀ +
− 137j₀ + 10j² − 21s₀ − l₀ − 5Kc²(17 + 20q₀ + 9q₀² − 2j₀)/(a₀²H₀²)] (10.50)–(10.51)."
`j²` is read as `j₀²`, "+ (newline) − 27j₀" as `− 27j₀` (same reading as C6, C7).
Definitions: (10.26)–(10.28) (`d_L = a₀(1+z) S_K(χ)`, `d_A = d_L/(1+z)²`, `χ = ∫ c dt/a`), the
review's (10.30) expands `r₀ = χ − Kχ³/3! + O(χ⁵)`.

Reading (charitable): the braces' `O(z⁵)` is a remainder `O(z⁶)` of `H₀d_L/c`; we claim only the
weaker `o(z⁵)`. The truncation `O(χ⁵)` in (10.30) does not license a printed `D⁴`: under a reading
"valid only to `O(χ⁵)`" (10.38) would have to end at `D³` with remainder `O(z⁴)` in the braces,
which is not what is printed. Every real `K`, every analytic, everywhere positive scale factor with
`H₀ > 0`; `D⁰…D³` and the rest of `D⁴` used as printed.

Conventions (as `Checked.Cosmography`): `c = 1`, `hubble`, `decel`, `cosmoCoeff`, `redshift`,
`comoving`, `transverse`, `lumDist` (`Checked.Cosmography.BambaK`), `angDist`
(`Checked.Cosmography.BambaA`).

FROZEN (annex 40.1) in run 2026-10-30T1232Z before proof work (commit 8c553aa).
PROMOTED from `Work/Cosmography/BambaZ.lean` (statements byte-identical); audit
`runs/2026-10-30T1232Z/audit.md`.

Referee notes (run 2026-10-30T1232Z, `runs/2026-10-30T1232Z/referee/`): (10.30)–(10.51) are verbatim
from Capozziello & Salzano 2009 (arXiv:0902.0088, Eqs. (31)–(52)); the sin/sinh truncation is from
Visser 2004 (gr-qc/0309109, Eq. (40)), where it is legitimate (series to `O(z⁴)` only). The upstream
site of the missing `k²/120` is `R⁴_D` ((10.36)). Under a reading "valid only to `O(χ⁵)`" the printed
`D⁴` would carry no information and the braces' remainder would be `O(z⁴)`; either way the printed
formula is wrong. Numerically negligible for `|Ω_k| ≲ 0.01`; in Milne the omitted term is the whole
error of the series (0.56 % at z = 1). The general theorem reuses the Checked y-series
(`lumDist_y_fifth_order`); the referee's sympy route (generic `C⁶` scale factor, direct inversion)
and exact models (Milne, `cosh t`, `sinh t`, Mattig dust) are independent.
-/

namespace Checked.Cosmography.BambaZ

open Filter Asymptotics Topology Checked.Cosmography Checked.Cosmography.Aviles
open Checked.Cosmography.BambaY Checked.Cosmography.BambaK Checked.Cosmography.BambaA
open scoped ContDiff

/-- `K c²/(H₀² a₀²)` (`c = 1`); the review's `Ω₀ = 1 + Kc²/(H₀²a₀²)` is `omega0`. -/
noncomputable def curvK (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) : ℝ :=
  K / (hubble a t₀ ^ 2 * a t₀ ^ 2)

/-- `D¹_L` as printed (Eq. (10.40)). -/
noncomputable def DL1z (q : ℝ) : ℝ := -(1 / 2) * (-1 + q)

/-- `D²_L` as printed (Eq. (10.41)), `k = Kc²/(H₀²a₀²)`. -/
noncomputable def DL2z (q j k : ℝ) : ℝ := -(1 / 6) * (1 - q - 3 * q ^ 2 + j + k)

/-- `D³_L` as printed (Eq. (10.42)). -/
noncomputable def DL3z (q j s k : ℝ) : ℝ :=
  (1 / 24) * (2 - 2 * q - 15 * q ^ 2 - 15 * q ^ 3 + 5 * j + 10 * q * j + s + 2 * k * (1 + 3 * q))

/-- `D⁴_L` as printed (Eqs. (10.43)–(10.44)), verbatim (`j² = j₀²`). -/
noncomputable def printedDL4z (q j s l k : ℝ) : ℝ :=
  (1 / 120) * (-6 + 6 * q + 81 * q ^ 2 + 165 * q ^ 3 + 105 * q ^ 4 - 110 * q * j
    - 105 * q ^ 2 * j - 15 * q * s + -27 * j + 10 * j ^ 2 - 11 * s - l
    - 5 * k * (1 + 8 * q + 9 * q ^ 2 - 2 * j))

/-- Proposed correction of (10.43)–(10.44): add `k²/120` (the `K²χ⁵/5!` term of `sin`/`sinh`). -/
noncomputable def correctDL4z (q j s l k : ℝ) : ℝ := printedDL4z q j s l k + k ^ 2 / 120

/-- `D¹_A` as printed (Eq. (10.47)). -/
noncomputable def DA1z (q : ℝ) : ℝ := -(1 / 2) * (3 + q)

/-- `D²_A` as printed (Eq. (10.48)). -/
noncomputable def DA2z (q j k : ℝ) : ℝ := (1 / 6) * (11 + 7 * q + 3 * q ^ 2 - j - k)

/-- `D³_A` as printed (Eq. (10.49)). -/
noncomputable def DA3z (q j s k : ℝ) : ℝ :=
  -(1 / 24) * (50 + 46 * q + 39 * q ^ 2 + 15 * q ^ 3 - 13 * j - 10 * q * j - s
    - 2 * k * (5 + 3 * q))

/-- `D⁴_A` as printed (Eqs. (10.50)–(10.51)), verbatim (`j² = j₀²`). -/
noncomputable def printedDA4z (q j s l k : ℝ) : ℝ :=
  (1 / 120) * (274 + 326 * q + 411 * q ^ 2 + 315 * q ^ 3 + 105 * q ^ 4 - 210 * q * j
    - 105 * q ^ 2 * j - 15 * q * s + -137 * j + 10 * j ^ 2 - 21 * s - l
    - 5 * k * (17 + 20 * q + 9 * q ^ 2 - 2 * j))

/-- Proposed correction of (10.50)–(10.51): add `k²/120`. -/
noncomputable def correctDA4z (q j s l k : ℝ) : ℝ := printedDA4z q j s l k + k ^ 2 / 120

/-- `z [1 + d₁ z + d₂ z² + d₃ z³ + d₄ z⁴]`. -/
noncomputable def seriesZ (d1 d2 d3 d4 z : ℝ) : ℝ :=
  z * (1 + d1 * z + d2 * z ^ 2 + d3 * z ^ 3 + d4 * z ^ 4)

/-- Remainder `H₀ d_L − z[1 + D¹_L z + … + D⁴ z⁴]`, printed `D¹…D³`, given `D⁴`. -/
noncomputable def remLz (D4 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  hubble a t₀ * lumDist K a t₀ t -
    seriesZ (DL1z (decel a t₀)) (DL2z (decel a t₀) (cosmoCoeff 3 a t₀) (curvK K a t₀))
      (DL3z (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (curvK K a t₀))
      (D4 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) (curvK K a t₀))
      (redshift a t₀ t)

/-- Remainder `H₀ d_A − z[1 + D¹_A z + … + D⁴ z⁴]`, printed `D¹…D³`, given `D⁴`. -/
noncomputable def remAz (D4 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  hubble a t₀ * angDist K a t₀ t -
    seriesZ (DA1z (decel a t₀)) (DA2z (decel a t₀) (cosmoCoeff 3 a t₀) (curvK K a t₀))
      (DA3z (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (curvK K a t₀))
      (D4 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) (curvK K a t₀))
      (redshift a t₀ t)

/-- Claim (10.38)–(10.44): printed `D⁰…D⁴_L`, remainder `o(z⁵)`, every `K`, every analytic,
everywhere positive scale factor with `H₀ > 0`. -/
def BambaDLzClaim : Prop :=
  ∀ (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), ContDiff ℝ ω a → (∀ t, 0 < a t) → 0 < hubble a t₀ →
    (fun t => remLz printedDL4z K a t₀ t) =o[𝓝 t₀] (fun t => redshift a t₀ t ^ 5)

/-- Claim (10.45)–(10.51): printed `D⁰…D⁴_A`, remainder `o(z⁵)`. -/
def BambaDAzClaim : Prop :=
  ∀ (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), ContDiff ℝ ω a → (∀ t, 0 < a t) → 0 < hubble a t₀ →
    (fun t => remAz printedDA4z K a t₀ t) =o[𝓝 t₀] (fun t => redshift a t₀ t ^ 5)

/-- Same claims, past emission only (`t < t₀`). -/
def BambaDLzClaimPast : Prop :=
  ∀ (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), ContDiff ℝ ω a → (∀ t, 0 < a t) → 0 < hubble a t₀ →
    (fun t => remLz printedDL4z K a t₀ t) =o[𝓝[<] t₀] (fun t => redshift a t₀ t ^ 5)

def BambaDAzClaimPast : Prop :=
  ∀ (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), ContDiff ℝ ω a → (∀ t, 0 < a t) → 0 < hubble a t₀ →
    (fun t => remAz printedDA4z K a t₀ t) =o[𝓝[<] t₀] (fun t => redshift a t₀ t ^ 5)

/-- The flat parts are right: at `K = 0` the corrections vanish. -/
theorem printed_flat_eq (q j s l : ℝ) :
    printedDL4z q j s l 0 = correctDL4z q j s l 0 ∧ printedDA4z q j s l 0 = correctDA4z q j s l 0 := by
  constructor <;> simp [correctDL4z, correctDA4z]

/-! ### Algebra (generated by `runs/2026-10-30T1232Z/scripts/gen_z.py`; Lean checks the identities) -/

/-- `(1+z)⁵ [S_y(z/(1+z)) − S_z(z)] = z⁶ W(z)`: `WL` for `d_L`, `WA` for `d_A`. -/
noncomputable def WL (q j s l Ω z : ℝ) : ℝ :=
  -Ω^2*z^4/120 - Ω^2*z^3/24 - Ω^2*z^2/12 - Ω^2*z/12 - Ω^2/24 - Ω*j*z^4/12 - 5*Ω*j*z^3/12 - 5*Ω*j*z^2/6 - 5*Ω*j*z/6 - 5*Ω*j/12 + 3*Ω*q^2*z^4/8 + 15*Ω*q^2*z^3/8 + 15*Ω*q^2*z^2/4 + 15*Ω*q^2*z/4 + 15*Ω*q^2/8 + Ω*q*z^4/3 + 17*Ω*q*z^3/12 + 25*Ω*q*z^2/12 + 5*Ω*q*z/6 - 5*Ω*q/6 + 7*Ω*z^4/120 + 5*Ω*z^3/24 + Ω*z^2/3 + 7*Ω*z/12 + 9*Ω/8 - j^2*z^4/12 - 5*j^2*z^3/12 - 5*j^2*z^2/6 - 5*j^2*z/6 - 5*j^2/12 + 7*j*q^2*z^4/8 + 35*j*q^2*z^3/8 + 35*j*q^2*z^2/4 + 35*j*q^2*z/4 + 35*j*q^2/8 + 11*j*q*z^4/12 + 25*j*q*z^3/6 + 85*j*q*z^2/12 + 5*j*q*z + 5*j*q/12 + 37*j*z^4/120 + 4*j*z^3/3 + 53*j*z^2/24 + 11*j*z/6 + 9*j/8 + l*z^4/120 + l*z^3/24 + l*z^2/12 + l*z/12 + l/24 - 7*q^4*z^4/8 - 35*q^4*z^3/8 - 35*q^4*z^2/4 - 35*q^4*z/4 - 35*q^4/8 - 11*q^3*z^4/8 - 25*q^3*z^3/4 - 85*q^3*z^2/8 - 15*q^3*z/2 - 5*q^3/8 - 21*q^2*z^4/20 - 37*q^2*z^3/8 - 63*q^2*z^2/8 - 27*q^2*z/4 - 4*q^2 + q*s*z^4/8 + 5*q*s*z^3/8 + 5*q*s*z^2/4 + 5*q*s*z/4 + 5*q*s/8 - 23*q*z^4/60 - 19*q*z^3/12 - 7*q*z^2/3 - 5*q*z/6 + 9*q/4 + 11*s*z^4/120 + 5*s*z^3/12 + 17*s*z^2/24 + s*z/2 + s/24 - z/2 - 7/2

noncomputable def WA (q j s l Ω z : ℝ) : ℝ :=
  -Ω^2*z^4/120 - Ω^2*z^3/24 - Ω^2*z^2/12 - Ω^2*z/12 - Ω^2/24 - Ω*j*z^4/12 - 5*Ω*j*z^3/12 - 5*Ω*j*z^2/6 - 5*Ω*j*z/6 - 5*Ω*j/12 + 3*Ω*q^2*z^4/8 + 15*Ω*q^2*z^3/8 + 15*Ω*q^2*z^2/4 + 15*Ω*q^2*z/4 + 15*Ω*q^2/8 + 5*Ω*q*z^4/6 + 47*Ω*q*z^3/12 + 85*Ω*q*z^2/12 + 35*Ω*q*z/6 + 5*Ω*q/3 + 29*Ω*z^4/40 + 77*Ω*z^3/24 + 16*Ω*z^2/3 + 47*Ω*z/12 + 9*Ω/8 - j^2*z^4/12 - 5*j^2*z^3/12 - 5*j^2*z^2/6 - 5*j^2*z/6 - 5*j^2/12 + 7*j*q^2*z^4/8 + 35*j*q^2*z^3/8 + 35*j*q^2*z^2/4 + 35*j*q^2*z/4 + 35*j*q^2/8 + 7*j*q*z^4/4 + 25*j*q*z^3/3 + 185*j*q*z^2/12 + 40*j*q*z/3 + 55*j*q/12 + 49*j*z^4/40 + 67*j*z^3/12 + 233*j*z^2/24 + 23*j*z/3 + 19*j/8 + l*z^4/120 + l*z^3/24 + l*z^2/12 + l*z/12 + l/24 - 7*q^4*z^4/8 - 35*q^4*z^3/8 - 35*q^4*z^2/4 - 35*q^4*z/4 - 35*q^4/8 - 21*q^3*z^4/8 - 25*q^3*z^3/2 - 185*q^3*z^2/8 - 20*q^3*z - 55*q^3/8 - 19*q^2*z^4/5 - 139*q^2*z^3/8 - 243*q^2*z^2/8 - 97*q^2*z/4 - 31*q^2/4 + q*s*z^4/8 + 5*q*s*z^3/8 + 5*q*s*z^2/4 + 5*q*s*z/4 + 5*q*s/8 - 71*q*z^4/20 - 187*q*z^3/12 - 155*q*z^2/6 - 115*q*z/6 - 21*q/4 + 7*s*z^4/40 + 5*s*z^3/6 + 37*s*z^2/24 + 4*s*z/3 + 11*s/24 - 3*z^4 - 25*z^3/2 - 39*z^2/2 - 27*z/2 - 7/2

lemma idZL (q j s l Ω z : ℝ) (hz : 1 + z ≠ 0) :
    seriesY4 q (correctD2y q j Ω) (correctD3y q j s Ω) (correctD4y q j s l Ω) (z / (1 + z))
      = seriesZ (DL1z q) (DL2z q j (Ω - 1)) (DL3z q j s (Ω - 1)) (correctDL4z q j s l (Ω - 1)) z
        + z ^ 6 * WL q j s l Ω z * (1 / (1 + z)) ^ 5 := by
  unfold seriesY4 D1y correctD2y correctD3y correctD4y printedD3y printedD4y seriesZ DL1z DL2z
    DL3z correctDL4z printedDL4z WL
  field_simp
  ring

lemma idZA (q j s l Ω z : ℝ) (hz : 1 + z ≠ 0) :
    z / (1 + z) * (1 + DA1 q * (z / (1 + z)) + DA2 q j Ω * (z / (1 + z)) ^ 2
        + correctDA3 q j s Ω * (z / (1 + z)) ^ 3 + correctDA4 q j s l Ω * (z / (1 + z)) ^ 4)
      = seriesZ (DA1z q) (DA2z q j (Ω - 1)) (DA3z q j s (Ω - 1)) (correctDA4z q j s l (Ω - 1)) z
        + z ^ 6 * WA q j s l Ω z * (1 / (1 + z)) ^ 5 := by
  unfold DA1 DA2 correctDA3 correctDA4 printedDA3 printedDA4 seriesZ DA1z DA2z DA3z correctDA4z
    printedDA4z WA
  field_simp
  ring

lemma cont_WL (q j s l Ω : ℝ) : Continuous (WL q j s l Ω) := by unfold WL; fun_prop
lemma cont_WA (q j s l Ω : ℝ) : Continuous (WA q j s l Ω) := by unfold WA; fun_prop

lemma curvK_eq (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) : curvK K a t₀ = omega0 K a t₀ - 1 := by
  simp [curvK, omega0]

lemma redshift_tendsto (a : ℝ → ℝ) (t₀ : ℝ) (hd : DifferentiableAt ℝ a t₀) (ha0 : a t₀ ≠ 0) :
    Tendsto (fun t => redshift a t₀ t) (𝓝 t₀) (𝓝 0) := by
  have h := (CCS.hasDerivAt_redshift a t₀ hd ha0).continuousAt.tendsto
  rwa [show redshift a t₀ t₀ = 0 by simp [redshift, ha0]] at h

/-- From `y` to `z`: if `R = o(y⁵)` and `R' = R + z⁶ W(z) (1/(1+z))⁵` near `t₀`, then
`R' = o(z⁵)`. -/
lemma transfer (a : ℝ → ℝ) (t₀ : ℝ) (hd : DifferentiableAt ℝ a t₀) (ha0 : a t₀ ≠ 0)
    {R R' W : ℝ → ℝ} (hW : Continuous W)
    (hR : R =o[𝓝 t₀] fun t => yred a t₀ t ^ 5)
    (hid : ∀ᶠ t in 𝓝 t₀, R' t = R t + redshift a t₀ t ^ 6 * W (redshift a t₀ t)
      * (1 / (1 + redshift a t₀ t)) ^ 5) :
    R' =o[𝓝 t₀] fun t => redshift a t₀ t ^ 5 := by
  have hz0 := redshift_tendsto a t₀ hd ha0
  have hu : (fun t => (1 / (1 + redshift a t₀ t)) ^ 5) =O[𝓝 t₀] (fun _ => (1 : ℝ)) := by
    have h1 : Tendsto (fun t => (1 / (1 + redshift a t₀ t)) ^ 5) (𝓝 t₀) (𝓝 ((1 / (1 + 0)) ^ 5)) :=
      ((tendsto_const_nhds.div (hz0.const_add 1) (by norm_num)).pow 5)
    exact h1.isBigO_one ℝ
  have hyz : (fun t => yred a t₀ t ^ 5) =O[𝓝 t₀] (fun t => redshift a t₀ t ^ 5) := by
    have := (isBigO_refl (fun t => redshift a t₀ t ^ 5) (𝓝 t₀)).mul hu
    refine (this.congr' (Eventually.of_forall fun t => ?_) (Eventually.of_forall fun t => ?_))
    · simp only [yred]; ring
    · simp
  have b1 := hR.trans_isBigO hyz
  have b2 : (fun t => redshift a t₀ t ^ 6 * W (redshift a t₀ t) * (1 / (1 + redshift a t₀ t)) ^ 5)
      =o[𝓝 t₀] (fun t => redshift a t₀ t ^ 5) := by
    have := (pow_succ_mul_isLittleO hz0 5 _ (CCS.bdd hz0 W hW)).mul_isBigO hu
    simpa using this
  exact (b1.add b2).congr' (hid.mono fun t ht => ht.symm) EventuallyEq.rfl

/-- `zⁿ` is not `o(zⁿ)` from the past (`H₀ ≠ 0`). -/
lemma not_isLittleO_self_past_z (a : ℝ → ℝ) (t₀ : ℝ) (hd : DifferentiableAt ℝ a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0) (n : ℕ) {c : ℝ} (hc : c ≠ 0)
    (h : (fun t => c * redshift a t₀ t ^ n) =o[𝓝[<] t₀] (fun t => redshift a t₀ t ^ n)) :
    False := by
  have hself : (fun t => redshift a t₀ t ^ n) =o[𝓝[<] t₀] (fun t => redshift a t₀ t ^ n) :=
    (h.const_mul_left c⁻¹).congr' (Eventually.of_forall fun t => by
      simp only; rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]) EventuallyEq.rfl
  have hev := (CCS.hasDerivAt_redshift a t₀ hd ha0).eventually_ne (c := 0) (neg_ne_zero.2 hH)
  have hev' : ∀ᶠ t in 𝓝[<] t₀, redshift a t₀ t ≠ 0 :=
    nhdsWithin_mono t₀ (fun t (ht : t < t₀) => ne_of_lt ht) hev
  have hfreq : ∃ᶠ t in 𝓝[<] t₀, ‖redshift a t₀ t ^ n‖ ≠ 0 :=
    (hev'.mono fun t ht => by simp [ht]).frequently
  exact isLittleO_irrefl' hfreq hself

lemma curvK_ne (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0)
    (hK : K ≠ 0) : curvK K a t₀ ^ 2 / 120 ≠ 0 :=
  div_ne_zero (pow_ne_zero 2 (div_ne_zero hK (mul_ne_zero (pow_ne_zero 2 hH)
    (pow_ne_zero 2 ha0)))) (by norm_num)

/-! ### Headline statements (frozen; proofs below the freeze) -/

/-- **Headline.** `d_L` to fifth order in `z` with the printed `D⁰…D³_L` and the corrected `D⁴_L`,
every `K`, every scale factor `C⁵` at `t₀` with `a(t₀) ≠ 0`, `H₀ ≠ 0`. -/
theorem lumDist_z_fifth_order (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 5 a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0) :
    (fun t => remLz correctDL4z K a t₀ t) =o[𝓝 t₀] (fun t => redshift a t₀ t ^ 5) := by
  have hd : DifferentiableAt ℝ a t₀ := ha.differentiableAt (by norm_num)
  have hne : ∀ᶠ t in 𝓝 t₀, a t ≠ 0 := hd.continuousAt.eventually_ne ha0
  refine transfer a t₀ hd ha0 (cont_WL (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀)
    (cosmoCoeff 5 a t₀) (omega0 K a t₀)) (lumDist_y_fifth_order K a t₀ ha ha0 hH) ?_
  filter_upwards [hne] with t ht
  have hw : 1 + redshift a t₀ t ≠ 0 := by
    simp only [redshift, add_sub_cancel]; exact div_ne_zero ha0 ht
  have hid := idZL (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀)
    (omega0 K a t₀) (redshift a t₀ t) hw
  simp only [remLz, remK, yred, curvK_eq]
  linear_combination hid

/-- **Headline.** Same for `d_A`. -/
theorem angDist_z_fifth_order (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 5 a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0) :
    (fun t => remAz correctDA4z K a t₀ t) =o[𝓝 t₀] (fun t => redshift a t₀ t ^ 5) := by
  have hd : DifferentiableAt ℝ a t₀ := ha.differentiableAt (by norm_num)
  have hne : ∀ᶠ t in 𝓝 t₀, a t ≠ 0 := hd.continuousAt.eventually_ne ha0
  refine transfer a t₀ hd ha0 (cont_WA (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀)
    (cosmoCoeff 5 a t₀) (omega0 K a t₀)) (angDist_y_fifth_order K a t₀ ha ha0 hH) ?_
  filter_upwards [hne] with t ht
  have hw : 1 + redshift a t₀ t ≠ 0 := by
    simp only [redshift, add_sub_cancel]; exact div_ne_zero ha0 ht
  have hid := idZA (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀)
    (omega0 K a t₀) (redshift a t₀ t) hw
  simp only [remAz, remA, yred, curvK_eq]
  linear_combination hid

/-- The printed `D⁴_L` fails, from the past, in every `C⁵` model with `a(t₀) ≠ 0`, `H₀ ≠ 0`,
`K ≠ 0`. -/
theorem printedDL4z_fails_past (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 5 a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0) (hK : K ≠ 0) :
    ¬ (fun t => remLz printedDL4z K a t₀ t) =o[𝓝[<] t₀] (fun t => redshift a t₀ t ^ 5) := by
  intro hp
  have hd : DifferentiableAt ℝ a t₀ := ha.differentiableAt (by norm_num)
  have hc := (lumDist_z_fifth_order K a t₀ ha ha0 hH).mono (nhdsWithin_le_nhds (s := Set.Iio t₀))
  have hdiff : (fun t => curvK K a t₀ ^ 2 / 120 * redshift a t₀ t ^ 5)
      =o[𝓝[<] t₀] (fun t => redshift a t₀ t ^ 5) := by
    refine (hp.sub hc).congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
    simp only [remLz, seriesZ, correctDL4z]; ring
  exact not_isLittleO_self_past_z a t₀ hd ha0 hH 5 (curvK_ne K a t₀ ha0 hH hK) hdiff

/-- The printed `D⁴_A` fails, from the past, in every `C⁵` model with `a(t₀) ≠ 0`, `H₀ ≠ 0`,
`K ≠ 0`. -/
theorem printedDA4z_fails_past (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 5 a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0) (hK : K ≠ 0) :
    ¬ (fun t => remAz printedDA4z K a t₀ t) =o[𝓝[<] t₀] (fun t => redshift a t₀ t ^ 5) := by
  intro hp
  have hd : DifferentiableAt ℝ a t₀ := ha.differentiableAt (by norm_num)
  have hc := (angDist_z_fifth_order K a t₀ ha ha0 hH).mono (nhdsWithin_le_nhds (s := Set.Iio t₀))
  have hdiff : (fun t => curvK K a t₀ ^ 2 / 120 * redshift a t₀ t ^ 5)
      =o[𝓝[<] t₀] (fun t => redshift a t₀ t ^ 5) := by
    refine (hp.sub hc).congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
    simp only [remAz, seriesZ, correctDA4z]; ring
  exact not_isLittleO_self_past_z a t₀ hd ha0 hH 5 (curvK_ne K a t₀ ha0 hH hK) hdiff

theorem bambaDLzClaim_false : ¬ BambaDLzClaim := by
  intro h
  exact printedDL4z_fails_past 1 Real.exp 0 Real.contDiff_exp.contDiffAt (Real.exp_pos 0).ne'
    (by rw [closedExp_vals.1]; norm_num) one_ne_zero
    ((h 1 Real.exp 0 Real.contDiff_exp Real.exp_pos (by rw [closedExp_vals.1]; norm_num)).mono (nhdsWithin_le_nhds (s := Set.Iio 0)))
theorem bambaDAzClaim_false : ¬ BambaDAzClaim := by
  intro h
  exact printedDA4z_fails_past 1 Real.exp 0 Real.contDiff_exp.contDiffAt (Real.exp_pos 0).ne'
    (by rw [closedExp_vals.1]; norm_num) one_ne_zero
    ((h 1 Real.exp 0 Real.contDiff_exp Real.exp_pos (by rw [closedExp_vals.1]; norm_num)).mono (nhdsWithin_le_nhds (s := Set.Iio 0)))
theorem bambaDLzClaimPast_false : ¬ BambaDLzClaimPast := by
  intro h
  exact printedDL4z_fails_past 1 Real.exp 0 Real.contDiff_exp.contDiffAt (Real.exp_pos 0).ne'
    (by rw [closedExp_vals.1]; norm_num) one_ne_zero
    (h 1 Real.exp 0 Real.contDiff_exp Real.exp_pos (by rw [closedExp_vals.1]; norm_num))
theorem bambaDAzClaimPast_false : ¬ BambaDAzClaimPast := by
  intro h
  exact printedDA4z_fails_past 1 Real.exp 0 Real.contDiff_exp.contDiffAt (Real.exp_pos 0).ne'
    (by rw [closedExp_vals.1]; norm_num) one_ne_zero
    (h 1 Real.exp 0 Real.contDiff_exp Real.exp_pos (by rw [closedExp_vals.1]; norm_num))

/-- Milne universe (`a = t`, `K = −1`, `t₀ = 1`; exact `H₀d_L = z + z²/2`): the printed `D⁴_L`
fails from the past (standalone instance; Milne is not positive for all `t`). -/
theorem milne_printedDL4z_fails_past :
    ¬ (fun t => remLz printedDL4z (-1) (fun t => t) 1 t)
      =o[𝓝[<] 1] (fun t => redshift (fun t => t) 1 t ^ 5) := by
  exact printedDL4z_fails_past (-1) (fun t => t) 1 contDiffAt_id one_ne_zero
    (by rw [milne_vals.1]; norm_num) (by norm_num)

end Checked.Cosmography.BambaZ
