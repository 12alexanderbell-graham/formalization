import Checked.Cosmography.BambaZ

/-!
# Candidates C15, C16: Demianski, Piedipalumbo, Sawant, Amati, A&A 598, A113 (2017),
arXiv:1609.09631 ("Cosmology with gamma-ray bursts II: cosmography challenges and cosmological
scenarios for the accelerated Universe"), Eqs. (13)–(23), p. 3; the `d_L` series reprinted in
Lusso, Piedipalumbo, Risaliti, Paolillo, Bisogni, Nardini, Amati, A&A 628, L4 (2019),
arXiv:1907.07692, Eqs. (2)–(6) and the unnumbered display after (6), p. 2

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

FROZEN (annex 40.1) in run 2026-10-30T1628Z before proof work (commit ab63005).

PROMOTED from `Work/Cosmography/DemianskiZ.lean` (statements byte-identical; two docstring
citations corrected per the referee); audit `runs/2026-10-30T1628Z/audit_c15.md`; blind closure
`Work/Cosmography/DemianskiZAudit.lean`.
Referee notes (`runs/2026-10-30T1628Z/referee_c15/referee_report.md`):
* The `D⁴_L` display carries no equation number in either paper (after (17) in Demianski et al.,
  after (6) in Lusso et al.; Lusso's Eq. (7) is the log-polynomial). Versions read: 1609.09631 v1, v2
  and 1907.07692 v1–v4, all with both errors.
* (23) is printed "… + 105q₀⁴ −" / "− 210q₀j₀ …" (a double minus across the line break); `demDA4`
  reads it as `− 210q₀j₀` (charitable; the literal `+ 210q₀j₀` reading is wrong as well).
* Provenance: the predecessor Demianski, Piedipalumbo, Rubano, Scudellaro 2012 (arXiv:1206.7046)
  Eqs. (41), (47) print the correct `+105q₀⁴`, `−137j₀`: both errors are new in 1609.09631;
  Lusso et al. 2019 copies the `d_L` one. No erratum found.
* Consequence: `l₀` enters only `D⁴`, linearly, so in a `d_L`-only fit with `l₀` free (Lusso et al.)
  the error is absorbed exactly by `l₀ ↦ l₀ − 210q₀⁴`: the reported `q₀, j₀, s₀` and the > 4σ claim
  are unaffected. In joint fits with `d_A` (BAO) and `H(z)` (Demianski et al.) the effect is
  undetermined. With `l₀` fixed the printed formula is off by `(7/4)q₀⁴z⁴` inside the bracket.
-/

namespace Checked.Cosmography.DemianskiZ

open Filter Asymptotics Topology Checked.Cosmography Checked.Cosmography.Aviles
open Checked.Cosmography.BambaZ
open scoped ContDiff

/-- `D⁴_L` as printed (Demianski et al. 2017, display after (17); Lusso et al. 2019, display after
(6)), verbatim. -/
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
  unfold correctDL4z correctDA4z printedDL4z printedDA4z demDL4 demDA4
  constructor <;> ring

/-- The printed `D⁴_L` fails, from the past, in every flat `C⁵` model with `a(t₀) ≠ 0`, `H₀ ≠ 0`,
`q₀ ≠ 0`. -/
theorem demDL4_fails_past (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 5 a t₀) (ha0 : a t₀ ≠ 0)
    (hH : hubble a t₀ ≠ 0) (hq : decel a t₀ ≠ 0) :
    ¬ (fun t => remLz (fun q j s l _ => demDL4 q j s l) 0 a t₀ t)
      =o[𝓝[<] t₀] (fun t => redshift a t₀ t ^ 5) := by
  intro hp
  have hd : DifferentiableAt ℝ a t₀ := ha.differentiableAt (by norm_num)
  have hc := (lumDist_z_fifth_order 0 a t₀ ha ha0 hH).mono (nhdsWithin_le_nhds (s := Set.Iio t₀))
  have hdiff : (fun t => (7 / 4 * decel a t₀ ^ 4) * redshift a t₀ t ^ 5)
      =o[𝓝[<] t₀] (fun t => redshift a t₀ t ^ 5) := by
    refine (hp.sub hc).congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
    have := (flat_corrections (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀)
      (cosmoCoeff 5 a t₀)).1
    have hk : curvK 0 a t₀ = 0 := by simp [curvK]
    simp only [remLz, seriesZ, hk]
    linear_combination (redshift a t₀ t ^ 5) * this
  exact not_isLittleO_self_past_z a t₀ hd ha0 hH 5
    (mul_ne_zero (by norm_num) (pow_ne_zero 4 hq)) hdiff

/-- The printed `D⁴_A` fails, from the past, in every flat `C⁵` model with `a(t₀) ≠ 0`, `H₀ ≠ 0`,
`j₀ ≠ 0`. -/
theorem demDA4_fails_past (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 5 a t₀) (ha0 : a t₀ ≠ 0)
    (hH : hubble a t₀ ≠ 0) (hj : cosmoCoeff 3 a t₀ ≠ 0) :
    ¬ (fun t => remAz (fun q j s l _ => demDA4 q j s l) 0 a t₀ t)
      =o[𝓝[<] t₀] (fun t => redshift a t₀ t ^ 5) := by
  intro hp
  have hd : DifferentiableAt ℝ a t₀ := ha.differentiableAt (by norm_num)
  have hc := (angDist_z_fifth_order 0 a t₀ ha ha0 hH).mono (nhdsWithin_le_nhds (s := Set.Iio t₀))
  have hdiff : (fun t => -(137 / 60 * cosmoCoeff 3 a t₀) * redshift a t₀ t ^ 5)
      =o[𝓝[<] t₀] (fun t => redshift a t₀ t ^ 5) := by
    refine (hp.sub hc).congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
    have := (flat_corrections (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀)
      (cosmoCoeff 5 a t₀)).2
    have hk : curvK 0 a t₀ = 0 := by simp [curvK]
    simp only [remAz, seriesZ, hk]
    linear_combination (redshift a t₀ t ^ 5) * this
  exact not_isLittleO_self_past_z a t₀ hd ha0 hH 5 (neg_ne_zero.2 (mul_ne_zero (by norm_num) hj)) hdiff

theorem demDLzClaim_false : ¬ DemDLzClaim := by
  intro h
  exact demDL4_fails_past Real.exp 0 Real.contDiff_exp.contDiffAt (Real.exp_pos 0).ne'
    (by rw [BambaY.deSitter_vals.1]; norm_num) (by rw [BambaY.deSitter_vals.2.1]; norm_num)
    ((h Real.exp 0 Real.contDiff_exp Real.exp_pos (by rw [BambaY.deSitter_vals.1]; norm_num)).mono
      (nhdsWithin_le_nhds (s := Set.Iio 0)))

theorem demDAzClaim_false : ¬ DemDAzClaim := by
  intro h
  exact demDA4_fails_past Real.exp 0 Real.contDiff_exp.contDiffAt (Real.exp_pos 0).ne'
    (by rw [BambaY.deSitter_vals.1]; norm_num) (by rw [BambaY.deSitter_vals.2.2]; norm_num)
    ((h Real.exp 0 Real.contDiff_exp Real.exp_pos (by rw [BambaY.deSitter_vals.1]; norm_num)).mono
      (nhdsWithin_le_nhds (s := Set.Iio 0)))

theorem demDLzClaimPast_false : ¬ DemDLzClaimPast := by
  intro h
  exact demDL4_fails_past Real.exp 0 Real.contDiff_exp.contDiffAt (Real.exp_pos 0).ne'
    (by rw [BambaY.deSitter_vals.1]; norm_num) (by rw [BambaY.deSitter_vals.2.1]; norm_num)
    (h Real.exp 0 Real.contDiff_exp Real.exp_pos (by rw [BambaY.deSitter_vals.1]; norm_num))

theorem demDAzClaimPast_false : ¬ DemDAzClaimPast := by
  intro h
  exact demDA4_fails_past Real.exp 0 Real.contDiff_exp.contDiffAt (Real.exp_pos 0).ne'
    (by rw [BambaY.deSitter_vals.1]; norm_num) (by rw [BambaY.deSitter_vals.2.2]; norm_num)
    (h Real.exp 0 Real.contDiff_exp Real.exp_pos (by rw [BambaY.deSitter_vals.1]; norm_num))

end Checked.Cosmography.DemianskiZ
