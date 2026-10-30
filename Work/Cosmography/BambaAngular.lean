import Work.Cosmography.BambaCurved

/-!
# Candidate C7: Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012),
arXiv:1205.3421v3, Sec. X, Eqs. (10.58)–(10.63): y-redshift angular-diameter-distance
coefficients `D_{A,y}` (verbatim also in Capozziello & Salzano 2009, arXiv:0902.0088, Eqs. (59)–(64))

Source (typeset, v1–v3 identical; `runs/2026-10-30T1028Z/typeset/cropA_pg_v3-111.png`,
`typeset/upstream_CapozzielloSalzano2009_0902.0088_p7_eqs59-69.png`):
"D⁰_{A,y} = 1, D¹_{A,y} = −½(1 + q₀), D²_{A,y} = −⅙(−q₀ − 3q₀² + j₀ + Ω₀),
D³_{A,y} = −(1/24)(−2q₀ + 3q₀² + 15q₀³ − j₀ − 10q₀j₀ − s₀ + 2Ω₀) (10.61),
D⁴_{A,y} = −(1/120)(1 − 6q₀ + 9q₀² − 15q₀³ − 105q₀⁴ + 10q₀j₀ + 105q₀²j₀ + 15q₀s₀ +
− 3j₀ − 10j² + s₀ + l₀ + 5Ω₀) (10.62)–(10.63). Previous relations have been derived for any value
of the curvature parameter." `j²` read as `j₀²`, "+ (10.62) − 3j₀" as `− 3j₀`.
Angular-diameter distance (10.27): `d_A = [a(t₀ − D/c)/a(t₀)] a(t₀) r₀ = d_L/(1+z)²`.

Reading as C6 (`Work.Cosmography.BambaK`): `d_A(y) = (cy/H₀)[D⁰ + D¹y + … + D⁴y⁴ + O(y⁵)]`.
The printed `D⁰…D²_{A,y}` are right, so the (10.61) claim uses them as printed; the (10.62)–(10.63)
claim also uses the corrected `D³_{A,y}` (charitable). Every real `K`; every analytic, everywhere
positive scale factor with `H₀ > 0`.

FROZEN (annex 40.1) in run 2026-10-30T1028Z before proof work.
-/

namespace Work.Cosmography.BambaA

open Filter Asymptotics Topology Checked.Cosmography Checked.Cosmography.Aviles
open Checked.Cosmography.BambaY Work.Cosmography.BambaK
open scoped ContDiff

/-- Angular-diameter distance `d_A = d_L/(1+z)²` (Eq. (10.27), `c = 1`). -/
noncomputable def angDist (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  lumDist K a t₀ t / (1 + redshift a t₀ t) ^ 2

/-- `D¹_{A,y}` as printed. -/
noncomputable def DA1 (q : ℝ) : ℝ := -(1 / 2) * (1 + q)

/-- `D²_{A,y}` as printed. -/
noncomputable def DA2 (q j Ω : ℝ) : ℝ := -(1 / 6) * (-q - 3 * q ^ 2 + j + Ω)

/-- `D³_{A,y}` as printed (Eq. (10.61)), verbatim. -/
noncomputable def printedDA3 (q j s Ω : ℝ) : ℝ :=
  -(1 / 24) * (-2 * q + 3 * q ^ 2 + 15 * q ^ 3 - j - 10 * q * j - s + 2 * Ω)

/-- `D⁴_{A,y}` as printed (Eqs. (10.62)–(10.63)), verbatim (`j² = j₀²`). -/
noncomputable def printedDA4 (q j s l Ω : ℝ) : ℝ :=
  -(1 / 120) * (1 - 6 * q + 9 * q ^ 2 - 15 * q ^ 3 - 105 * q ^ 4 + 10 * q * j + 105 * q ^ 2 * j
    + 15 * q * s + -3 * j - 10 * j ^ 2 + s + l + 5 * Ω)

/-- Proposed correction of (10.61): add `q₀(Ω₀ − 1)/4`. -/
noncomputable def correctDA3 (q j s Ω : ℝ) : ℝ :=
  printedDA3 q j s Ω + q * (Ω - 1) / 4

/-- Proposed correction of (10.62)–(10.63): add `(Ω₀ − 1)[(Ω₀ − 1) + 10j₀ − 45q₀² + 20q₀]/120`. -/
noncomputable def correctDA4 (q j s l Ω : ℝ) : ℝ :=
  printedDA4 q j s l Ω + (Ω - 1) * ((Ω - 1) + 10 * j - 45 * q ^ 2 + 20 * q) / 120

/-- Remainder `H₀ d_A − y[1 + D¹_A y + D²_A y² + D³ y³ + D⁴ y⁴]` for curvature `K`. -/
noncomputable def remA (D3 : ℝ → ℝ → ℝ → ℝ → ℝ) (D4 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ)
    (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  hubble a t₀ * angDist K a t₀ t -
    yred a t₀ t * (1 + DA1 (decel a t₀) * yred a t₀ t
      + DA2 (decel a t₀) (cosmoCoeff 3 a t₀) (omega0 K a t₀) * yred a t₀ t ^ 2
      + D3 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (omega0 K a t₀) * yred a t₀ t ^ 3
      + D4 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀)
          (omega0 K a t₀) * yred a t₀ t ^ 4)

/-- Claim (10.61): printed `D⁰…D³_{A,y}`, remainder `o(y⁴)`, every `K`, every analytic, everywhere
positive scale factor with `H₀ > 0`. -/
def BambaDA3Claim : Prop :=
  ∀ (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), ContDiff ℝ ω a → (∀ t, 0 < a t) → 0 < hubble a t₀ →
    (fun t => remA printedDA3 (fun _ _ _ _ _ => 0) K a t₀ t) =o[𝓝 t₀] (fun t => yred a t₀ t ^ 4)

/-- Claim (10.62)–(10.63), charitable: corrected `D³_{A,y}`, printed `D⁴_{A,y}`, `o(y⁵)`. -/
def BambaDA4Claim : Prop :=
  ∀ (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), ContDiff ℝ ω a → (∀ t, 0 < a t) → 0 < hubble a t₀ →
    (fun t => remA correctDA3 printedDA4 K a t₀ t) =o[𝓝 t₀] (fun t => yred a t₀ t ^ 5)

/-- Same claims, past emission only. -/
def BambaDA3ClaimPast : Prop :=
  ∀ (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), ContDiff ℝ ω a → (∀ t, 0 < a t) → 0 < hubble a t₀ →
    (fun t => remA printedDA3 (fun _ _ _ _ _ => 0) K a t₀ t) =o[𝓝[<] t₀] (fun t => yred a t₀ t ^ 4)

def BambaDA4ClaimPast : Prop :=
  ∀ (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), ContDiff ℝ ω a → (∀ t, 0 < a t) → 0 < hubble a t₀ →
    (fun t => remA correctDA3 printedDA4 K a t₀ t) =o[𝓝[<] t₀] (fun t => yred a t₀ t ^ 5)

/-- **Headline (to prove).** Angular-diameter distance to fifth order in `y`, every `K`, every
scale factor `C⁵` at `t₀` with `a(t₀) ≠ 0`, `H₀ ≠ 0`. -/
theorem angDist_y_fifth_order (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 5 a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0) :
    (fun t => remA correctDA3 correctDA4 K a t₀ t) =o[𝓝 t₀] (fun t => yred a t₀ t ^ 5) := by
  sorry

theorem bambaDA3Claim_false : ¬ BambaDA3Claim := by
  sorry

theorem bambaDA4Claim_false : ¬ BambaDA4Claim := by
  sorry

theorem bambaDA3ClaimPast_false : ¬ BambaDA3ClaimPast := by
  sorry

theorem bambaDA4ClaimPast_false : ¬ BambaDA4ClaimPast := by
  sorry

end Work.Cosmography.BambaA
