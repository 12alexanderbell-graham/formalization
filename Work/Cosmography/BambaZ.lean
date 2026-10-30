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

FROZEN (annex 40.1) in run 2026-10-30T1232Z before proof work.
-/

namespace Work.Cosmography.BambaZ

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

/-! ### Headline statements (frozen; proofs below the freeze) -/

/-- **Headline.** `d_L` to fifth order in `z` with the printed `D⁰…D³_L` and the corrected `D⁴_L`,
every `K`, every scale factor `C⁵` at `t₀` with `a(t₀) ≠ 0`, `H₀ ≠ 0`. -/
theorem lumDist_z_fifth_order (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 5 a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0) :
    (fun t => remLz correctDL4z K a t₀ t) =o[𝓝 t₀] (fun t => redshift a t₀ t ^ 5) := by
  sorry

/-- **Headline.** Same for `d_A`. -/
theorem angDist_z_fifth_order (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 5 a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0) :
    (fun t => remAz correctDA4z K a t₀ t) =o[𝓝 t₀] (fun t => redshift a t₀ t ^ 5) := by
  sorry

/-- The printed `D⁴_L` fails, from the past, in every `C⁵` model with `a(t₀) ≠ 0`, `H₀ ≠ 0`,
`K ≠ 0`. -/
theorem printedDL4z_fails_past (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 5 a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0) (hK : K ≠ 0) :
    ¬ (fun t => remLz printedDL4z K a t₀ t) =o[𝓝[<] t₀] (fun t => redshift a t₀ t ^ 5) := by
  sorry

/-- The printed `D⁴_A` fails, from the past, in every `C⁵` model with `a(t₀) ≠ 0`, `H₀ ≠ 0`,
`K ≠ 0`. -/
theorem printedDA4z_fails_past (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 5 a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0) (hK : K ≠ 0) :
    ¬ (fun t => remAz printedDA4z K a t₀ t) =o[𝓝[<] t₀] (fun t => redshift a t₀ t ^ 5) := by
  sorry

theorem bambaDLzClaim_false : ¬ BambaDLzClaim := by sorry
theorem bambaDAzClaim_false : ¬ BambaDAzClaim := by sorry
theorem bambaDLzClaimPast_false : ¬ BambaDLzClaimPast := by sorry
theorem bambaDAzClaimPast_false : ¬ BambaDAzClaimPast := by sorry

/-- Milne universe (`a = t`, `K = −1`, `t₀ = 1`; exact `H₀d_L = z + z²/2`): the printed `D⁴_L`
fails from the past (standalone instance; Milne is not positive for all `t`). -/
theorem milne_printedDL4z_fails_past :
    ¬ (fun t => remLz printedDL4z (-1) (fun t => t) 1 t)
      =o[𝓝[<] 1] (fun t => redshift (fun t => t) 1 t ^ 5) := by
  sorry

end Work.Cosmography.BambaZ
