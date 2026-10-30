import Checked.Cosmography.BambaZ

/-!
# Candidates C15, C16: Demianski, Piedipalumbo, Sawant, Amati, A&A 598, A113 (2017),
arXiv:1609.09631 ("Cosmology with gamma-ray bursts II: cosmography challenges and cosmological
scenarios for the accelerated Universe"), Eqs. (13)–(23), p. 3; the `d_L` series reprinted in
Lusso, Piedipalumbo, Risaliti, Paolillo, Bisogni, Nardini, Amati, A&A 628, L4 (2019),
arXiv:1907.07692, Eqs. (2)–(7), p. 2

Source (typeset crops `runs/2026-10-30T1628Z/screen/DEM17b_p3_eqs13-23.png`,
`runs/2026-10-30T1628Z/screen/L19_p2_eqs2-7_DL_z.png`, read by the screen subagent and by the main
session):
"d_L(z) = (cz/H₀)(D⁰_L + D¹_L z + D²_L z² + D³_L z³ + D⁴_L z⁴ + O(z⁵)), D⁰_L = 1,
D¹_L = −½(−1 + q₀), D²_L = −⅙(1 − q₀ − 3q₀² + j₀), D³_L = (1/24)(2 − 2q₀ − 15q₀² − 15q₀³ + 5j₀
+ 10q₀j₀ + s₀), D⁴_L = (1/120)(−6 + 6q₀ + 81q₀² + 165q₀³ − 105q₀⁴ − 110q₀j₀ + − 105q₀²j₀ − 15q₀s₀
− 27j₀ + 10j² − 11s₀ − l₀)" (Lusso et al.: identical, `10j₀²`);
"d_A(z) = (cz/H₀)(D⁰_A + D¹_A z + … + D⁴_A z⁴ + O(z⁵)), D⁰_A = 1, D¹_A = −½(3 + q₀),
D²_A = ⅙(11 + 7q₀ + 3q₀² − j₀), D³_A = −(1/24)(50 + 46q₀ + 39q₀² + 15q₀³ − 13j₀ − 10q₀j₀ − s₀ +
− 2kc²(5 + 3q₀)/(H₀²a₀²)), D⁴_A = (1/120)(274 + 326q₀ + 411q₀² + 315q₀³ + 105q₀⁴ − 210q₀j₀
− 105q₀²j₀ − 15q₀s₀ + 137j₀ + 10j₀² − 21s₀ − l₀)".
Readings: `j² = j₀²`; "+ (newline) − 105q₀²j₀" as `− 105q₀²j₀`. The `d_L` series carries no
curvature terms, `d_A` carries one only in `D³_A`: we formalize the flat case (`K = 0`), where the
printed `D⁰…D³` coincide with the Checked ones (`Checked.Cosmography.BambaZ.DL1z … DA3z` at
`k = 0`).

Claims frozen: the printed `D⁴_L` and `D⁴_A`, as `o(z⁵)` remainders (the charitable reading of
`O(z⁵)` inside the bracket), for every analytic, everywhere positive flat scale factor with
`H₀ > 0`, two-sided and past-only. Correct values: `Checked.Cosmography.BambaZ.correctDL4z`,
`correctDA4z` at `k = 0` (`lumDist_z_fifth_order`, `angDist_z_fifth_order`).

Conventions as `Checked.Cosmography` (`c = 1`; `lumDist 0`, `angDist 0` are the flat distances).

FROZEN (annex 40.1) in run 2026-10-30T1628Z before proof work.
-/

namespace Work.Cosmography.DemianskiZ

open Filter Asymptotics Topology Checked.Cosmography Checked.Cosmography.Aviles
open Checked.Cosmography.BambaZ
open scoped ContDiff

/-- `D⁴_L` as printed (Demianski et al. 2017 (13)ff., Lusso et al. 2019 (7)), verbatim. -/
noncomputable def demDL4 (q j s l : ℝ) : ℝ :=
  (1 / 120) * (-6 + 6 * q + 81 * q ^ 2 + 165 * q ^ 3 - 105 * q ^ 4 - 110 * q * j
    + -105 * q ^ 2 * j - 15 * q * s - 27 * j + 10 * j ^ 2 - 11 * s - l)

/-- `D⁴_A` as printed (Demianski et al. 2017 (23)), verbatim. -/
noncomputable def demDA4 (q j s l : ℝ) : ℝ :=
  (1 / 120) * (274 + 326 * q + 411 * q ^ 2 + 315 * q ^ 3 + 105 * q ^ 4 - 210 * q * j
    - 105 * q ^ 2 * j - 15 * q * s + 137 * j + 10 * j ^ 2 - 21 * s - l)

/-- Printed `d_L(z)` series, flat, remainder `o(z⁵)`, every analytic positive scale factor. -/
def DemDLzClaim : Prop :=
  ∀ (a : ℝ → ℝ) (t₀ : ℝ), ContDiff ℝ ω a → (∀ t, 0 < a t) → 0 < hubble a t₀ →
    (fun t => remLz (fun q j s l _ => demDL4 q j s l) 0 a t₀ t)
      =o[𝓝 t₀] (fun t => redshift a t₀ t ^ 5)

/-- Printed `d_A(z)` series, flat. -/
def DemDAzClaim : Prop :=
  ∀ (a : ℝ → ℝ) (t₀ : ℝ), ContDiff ℝ ω a → (∀ t, 0 < a t) → 0 < hubble a t₀ →
    (fun t => remAz (fun q j s l _ => demDA4 q j s l) 0 a t₀ t)
      =o[𝓝 t₀] (fun t => redshift a t₀ t ^ 5)

/-- Same, past emission only. -/
def DemDLzClaimPast : Prop :=
  ∀ (a : ℝ → ℝ) (t₀ : ℝ), ContDiff ℝ ω a → (∀ t, 0 < a t) → 0 < hubble a t₀ →
    (fun t => remLz (fun q j s l _ => demDL4 q j s l) 0 a t₀ t)
      =o[𝓝[<] t₀] (fun t => redshift a t₀ t ^ 5)

def DemDAzClaimPast : Prop :=
  ∀ (a : ℝ → ℝ) (t₀ : ℝ), ContDiff ℝ ω a → (∀ t, 0 < a t) → 0 < hubble a t₀ →
    (fun t => remAz (fun q j s l _ => demDA4 q j s l) 0 a t₀ t)
      =o[𝓝[<] t₀] (fun t => redshift a t₀ t ^ 5)

/-! ### Headline statements (frozen) -/

/-- The printed coefficients against the correct flat ones: `D⁴_L` misses `+(7/4)q₀⁴`
(`−105q₀⁴` for `+105q₀⁴`), `D⁴_A` has `+(137/60)j₀` too much (`+137j₀` for `−137j₀`). -/
theorem flat_corrections (q j s l : ℝ) :
    correctDL4z q j s l 0 - demDL4 q j s l = 7 / 4 * q ^ 4 ∧
    correctDA4z q j s l 0 - demDA4 q j s l = -(137 / 60) * j := by
  sorry

/-- The printed `D⁴_L` fails, from the past, in every flat `C⁵` model with `a(t₀) ≠ 0`, `H₀ ≠ 0`,
`q₀ ≠ 0`. -/
theorem demDL4_fails_past (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 5 a t₀) (ha0 : a t₀ ≠ 0)
    (hH : hubble a t₀ ≠ 0) (hq : decel a t₀ ≠ 0) :
    ¬ (fun t => remLz (fun q j s l _ => demDL4 q j s l) 0 a t₀ t)
      =o[𝓝[<] t₀] (fun t => redshift a t₀ t ^ 5) := by
  sorry

/-- The printed `D⁴_A` fails, from the past, in every flat `C⁵` model with `a(t₀) ≠ 0`, `H₀ ≠ 0`,
`j₀ ≠ 0`. -/
theorem demDA4_fails_past (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 5 a t₀) (ha0 : a t₀ ≠ 0)
    (hH : hubble a t₀ ≠ 0) (hj : cosmoCoeff 3 a t₀ ≠ 0) :
    ¬ (fun t => remAz (fun q j s l _ => demDA4 q j s l) 0 a t₀ t)
      =o[𝓝[<] t₀] (fun t => redshift a t₀ t ^ 5) := by
  sorry

theorem demDLzClaim_false : ¬ DemDLzClaim := by
  sorry

theorem demDAzClaim_false : ¬ DemDAzClaim := by
  sorry

theorem demDLzClaimPast_false : ¬ DemDLzClaimPast := by
  sorry

theorem demDAzClaimPast_false : ¬ DemDAzClaimPast := by
  sorry

end Work.Cosmography.DemianskiZ
