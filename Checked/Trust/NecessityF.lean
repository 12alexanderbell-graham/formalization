import Checked.Trust.NonVacuity
import Checked.Trust.Witnesses
import Checked.Records.Findings
import Checked.Cosmography.LCDMCoefficients
import Checked.Cosmography.CPLCoefficients
import Checked.Chemistry.CubicEOS
import Checked.Sim.Duffing
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Necessity of each part of a bundled hypothesis (trust track T2b item 3e, runs 2026-11-11T1428Z, 1628Z)

Blind red team AF (run 2026-11-11T0428Z) showed that a hypothesis which bundles several conditions behind a
program definition is classified only as a bundle: `necessity% thm i` says that *some* part of it matters,
not that each does. The obligation `necessity% thm i j` (`Checked/Trust/NonVacuity.lean`) asks for data
meeting every other hypothesis and hypothesis `i` with its `j`-th *part* replaced by `True`, with the
conclusion false; `dropped% thm i j` is the statement with that part dropped. Parts are reached through
`∧`, `∃`, `∀`, `∀ᶠ` and an implication's conclusion (`Checked.Trust.partsWalk`), so a conjunction under a
binder (the law's `a > 0 ∧ differentiable ∧ law` under `∀ᶠ`) is split too. `scripts/trust/StatementDeps.lean`
drops `bundled i` from the trust map once every part is witnessed.

Witnesses, by family:
* **Cosmography** (`IsFlatLCDM`, `IsFlatCPL`: parts `0 < H₀`; near t₀, `a > 0`; `a` differentiable; the
  expansion law): `0 < H₀` is needed (the static model `a ≡ 1` meets the rest and every junk coefficient is
  zero); the law is needed (de Sitter); positivity of `a` and differentiability are REDUNDANT: the other
  parts force differentiability near t₀ (a junk derivative would make the Hubble rate vanish where the law
  makes it positive), and force a sign of `a` near t₀, while every coefficient is unchanged by `a ↦ -a`.
* **Critical point of a cubic isotherm** (`IsCriticalIsotherm p v`: slope and curvature vanish): each
  condition alone fixes a temperature at which the other fails and the compressibility factor is not the
  critical value (the numbers are in each docstring).
* **Duffing initial-value problem**: without the initial position the rest state solves the rest; without
  the velocity equation a parabola with the right initial data is negative before the certified first
  zero. The parts "initial velocity" and "position equation" are open, so the hypothesis stays bundled.
-/

open Set Filter Topology

namespace Checked.Trust.NCF

section Cosmography
open Checked.Records Checked.Cosmography Checked.Cosmography.Aviles Checked.Trust.NV

theorem st_hubble (t : ℝ) : hubble (fun _ : ℝ => (1 : ℝ)) t = 0 := by simp [hubble]

theorem st_coeff (n : ℕ) (hn : 0 < n) (t : ℝ) : cosmoCoeff n (fun _ : ℝ => (1 : ℝ)) t = 0 := by
  simp [cosmoCoeff, st_hubble, zero_pow hn.ne']

theorem st_decel (t : ℝ) : decel (fun _ : ℝ => (1 : ℝ)) t = 0 := by simp [decel]

/-- The static model meets every expansion law of the form `H(t) = H(t₀) · g(t)` near any t₀. -/
theorem st_law (t₀ : ℝ) (g : ℝ → ℝ) :
    ∀ᶠ t in 𝓝 t₀, 0 < (fun _ : ℝ => (1 : ℝ)) t ∧ DifferentiableAt ℝ (fun _ : ℝ => (1 : ℝ)) t ∧
      hubble (fun _ : ℝ => (1 : ℝ)) t = hubble (fun _ : ℝ => (1 : ℝ)) t₀ * g t :=
  Eventually.of_forall fun t => ⟨one_pos, differentiableAt_const _, by simp [st_hubble]⟩

theorem dS_H_pos : 0 < hubble Real.exp 0 := by rw [dS_hubble]; norm_num

theorem dS_ev : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < Real.exp t ∧ DifferentiableAt ℝ Real.exp t :=
  Eventually.of_forall fun t => ⟨Real.exp_pos t, Real.differentiableAt_exp⟩


/-! Generic redundancy of the parts `0 < a t` and `DifferentiableAt ℝ a t` of a flat expansion law. -/

theorem hubble_neg (a : ℝ → ℝ) (t : ℝ) : hubble (fun s => -a s) t = hubble a t := by
  simp only [hubble, deriv.fun_neg, neg_div_neg_eq]

theorem redshift_neg (a : ℝ → ℝ) (t₀ t : ℝ) : redshift (fun s => -a s) t₀ t = redshift a t₀ t := by
  simp only [redshift, neg_div_neg_eq]

theorem decel_neg (a : ℝ → ℝ) (t : ℝ) : decel (fun s => -a s) t = decel a t := by
  have h1 : deriv (fun s => -a s) = fun s => -deriv a s := funext fun s => deriv.fun_neg
  simp only [decel, h1, deriv.fun_neg]
  ring

theorem cosmoCoeff_neg (n : ℕ) (a : ℝ → ℝ) (t : ℝ) :
    cosmoCoeff n (fun s => -a s) t = cosmoCoeff n a t := by
  simp only [cosmoCoeff, iteratedDeriv_fun_neg, hubble_neg]
  rw [neg_mul, neg_div_neg_eq]

/-- A law `H(t) = H(t₀) g(z(t))` with `g` continuous at `0`, `g 0 = 1`, and `H(t₀) > 0` makes `a`
differentiable near `t₀` (a junk derivative 0 would give `H = 0` where `g > 0`). -/
theorem eventually_diff_of_law {a : ℝ → ℝ} {t₀ : ℝ} {g : ℝ → ℝ} (hg : ContinuousAt g 0) (hg0 : g 0 = 1)
    (hH : 0 < hubble a t₀) (hlaw : ∀ᶠ t in 𝓝 t₀, hubble a t = hubble a t₀ * g (redshift a t₀ t)) :
    ∀ᶠ t in 𝓝 t₀, DifferentiableAt ℝ a t := by
  have hd0 : deriv a t₀ ≠ 0 := by
    intro h; simp [hubble, h] at hH
  have ha0 : a t₀ ≠ 0 := by
    intro h; simp [hubble, h] at hH
  have hdiff : DifferentiableAt ℝ a t₀ := by
    by_contra hn; exact hd0 (deriv_zero_of_not_differentiableAt hn)
  have hz : Tendsto (fun t => redshift a t₀ t) (𝓝 t₀) (𝓝 0) := by
    have : Tendsto (fun t => a t₀ / a t - 1) (𝓝 t₀) (𝓝 (a t₀ / a t₀ - 1)) :=
      ((tendsto_const_nhds.div hdiff.continuousAt.tendsto ha0).sub tendsto_const_nhds)
    simpa [redshift, div_self ha0] using this
  have hgpos : ∀ᶠ t in 𝓝 t₀, 0 < g (redshift a t₀ t) := by
    have : Tendsto (fun t => g (redshift a t₀ t)) (𝓝 t₀) (𝓝 1) := by
      rw [← hg0]; exact hg.tendsto.comp hz
    exact this.eventually (lt_mem_nhds one_pos)
  filter_upwards [hlaw, hgpos] with t ht hp
  by_contra hn
  have : hubble a t = 0 := by simp [hubble, deriv_zero_of_not_differentiableAt hn]
  rw [this] at ht
  have : 0 < hubble a t₀ * g (redshift a t₀ t) := mul_pos hH hp
  linarith

/-- With `H(t₀) > 0` and `a` differentiable near `t₀`, either `a > 0` near `t₀` or `-a > 0` near `t₀`. -/
theorem eventually_sign {a : ℝ → ℝ} {t₀ : ℝ} (hH : 0 < hubble a t₀)
    (hd : ∀ᶠ t in 𝓝 t₀, DifferentiableAt ℝ a t) :
    (∀ᶠ t in 𝓝 t₀, 0 < a t) ∨ (∀ᶠ t in 𝓝 t₀, 0 < -a t) := by
  have ha0 : a t₀ ≠ 0 := by
    intro h; simp [hubble, h] at hH
  have hc : ContinuousAt a t₀ := hd.self_of_nhds.continuousAt
  rcases lt_or_gt_of_ne ha0 with h | h
  · right; exact hc.eventually (gt_mem_nhds h) |>.mono fun t ht => by linarith
  · left; exact hc.eventually (lt_mem_nhds h)


/-- The flat ΛCDM law with the part `0 < a t` dropped holds for `a` or for `-a`. -/
theorem lcdm_noPos {Ω : ℝ} {a : ℝ → ℝ} {t₀ : ℝ}
    (h : 0 < hubble a t₀ ∧ ∀ᶠ t in 𝓝 t₀, DifferentiableAt ℝ a t ∧
      hubble a t = hubble a t₀ * √(Ω * (1 + redshift a t₀ t) ^ 3 + 1 - Ω)) :
    IsFlatLCDM Ω a t₀ ∨ IsFlatLCDM Ω (fun s => -a s) t₀ := by
  obtain ⟨hH, hev⟩ := h
  rcases eventually_sign hH (hev.mono fun t h => h.1) with hp | hn
  · exact Or.inl ⟨hH, (hp.and hev).mono fun t ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩⟩
  · refine Or.inr ⟨by rwa [hubble_neg], (hn.and hev).mono fun t ⟨h1, h2, h3⟩ => ⟨h1, h2.neg, ?_⟩⟩
    rw [hubble_neg, hubble_neg, redshift_neg]; exact h3

/-- The flat ΛCDM law with the part `DifferentiableAt ℝ a t` dropped still holds. -/
theorem lcdm_noDiff {Ω : ℝ} {a : ℝ → ℝ} {t₀ : ℝ}
    (h : 0 < hubble a t₀ ∧ ∀ᶠ t in 𝓝 t₀, 0 < a t ∧
      hubble a t = hubble a t₀ * √(Ω * (1 + redshift a t₀ t) ^ 3 + 1 - Ω)) :
    IsFlatLCDM Ω a t₀ := by
  obtain ⟨hH, hev⟩ := h
  have hd := eventually_diff_of_law (g := fun z => √(Ω * (1 + z) ^ 3 + 1 - Ω)) (by fun_prop)
    (by norm_num) hH (hev.mono fun t h => h.2)
  exact ⟨hH, (hev.and hd).mono fun t ⟨⟨h1, h3⟩, h2⟩ => ⟨h1, h2, h3⟩⟩

/-- The same for flat CPL, part `0 < a t` dropped. -/
theorem cpl_noPos {Ω w₀ wₐ : ℝ} {a : ℝ → ℝ} {t₀ : ℝ}
    (h : 0 < hubble a t₀ ∧ ∀ᶠ t in 𝓝 t₀, DifferentiableAt ℝ a t ∧
      hubble a t = hubble a t₀ * √(Ω * (1 + redshift a t₀ t) ^ 3 +
      (1 - Ω) * (1 + redshift a t₀ t) ^ (3 * (1 + w₀ + wₐ)) *
        Real.exp (-(3 * wₐ * redshift a t₀ t) / (1 + redshift a t₀ t)))) :
    CPL.IsFlatCPL Ω w₀ wₐ a t₀ ∨ CPL.IsFlatCPL Ω w₀ wₐ (fun s => -a s) t₀ := by
  obtain ⟨hH, hev⟩ := h
  rcases eventually_sign hH (hev.mono fun t h => h.1) with hp | hn
  · exact Or.inl ⟨hH, (hp.and hev).mono fun t ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩⟩
  · refine Or.inr ⟨by rwa [hubble_neg], (hn.and hev).mono fun t ⟨h1, h2, h3⟩ => ⟨h1, h2.neg, ?_⟩⟩
    rw [hubble_neg, hubble_neg, redshift_neg]; exact h3

/-- The same for flat CPL, part `DifferentiableAt ℝ a t` dropped. -/
theorem cpl_noDiff {Ω w₀ wₐ : ℝ} {a : ℝ → ℝ} {t₀ : ℝ}
    (h : 0 < hubble a t₀ ∧ ∀ᶠ t in 𝓝 t₀, 0 < a t ∧
      hubble a t = hubble a t₀ * √(Ω * (1 + redshift a t₀ t) ^ 3 +
      (1 - Ω) * (1 + redshift a t₀ t) ^ (3 * (1 + w₀ + wₐ)) *
        Real.exp (-(3 * wₐ * redshift a t₀ t) / (1 + redshift a t₀ t)))) :
    CPL.IsFlatCPL Ω w₀ wₐ a t₀ := by
  obtain ⟨hH, hev⟩ := h
  have hg : ContinuousAt (fun z : ℝ => √(Ω * (1 + z) ^ 3 + (1 - Ω) * (1 + z) ^ (3 * (1 + w₀ + wₐ)) *
      Real.exp (-(3 * wₐ * z) / (1 + z)))) 0 := by
    have h1 : ContinuousAt (fun z : ℝ => (1 + z) ^ (3 * (1 + w₀ + wₐ))) 0 :=
      (continuousAt_const.add continuousAt_id).rpow_const (Or.inl (by norm_num))
    have h2 : ContinuousAt (fun z : ℝ => -(3 * wₐ * z) / (1 + z)) 0 :=
      (continuousAt_const.mul continuousAt_id).neg.div (continuousAt_const.add continuousAt_id)
        (by norm_num)
    exact ((continuousAt_const.mul ((continuousAt_const.add continuousAt_id).pow 3)).add
      ((continuousAt_const.mul h1).mul (Real.continuous_exp.continuousAt.comp h2))).sqrt
  have hd := eventually_diff_of_law hg (by norm_num) hH (hev.mono fun t h => h.2)
  exact ⟨hH, (hev.and hd).mono fun t ⟨⟨h1, h3⟩, h2⟩ => ⟨h1, h2, h3⟩⟩


/-! Parts 2 (`0 < a t` near t₀) and 3 (`a` differentiable near t₀) of the flat ΛCDM/CPL laws are
REDUNDANT: the other parts force them for `a` or for `-a` (`lcdm_noPos`, `cpl_noPos`, `lcdm_noDiff`,
`cpl_noDiff`), and every coefficient is unchanged by `a ↦ -a`. -/

theorem flatLCDM_coeffs_p1_2 : dropped% Checked.Cosmography.Aviles.flatLCDM_coeffs 1 2 := by
  intro Ω a t₀ hs h
  rcases lcdm_noPos h with hL | hL
  · exact flatLCDM_coeffs Ω a t₀ hL hs
  · simpa only [decel_neg, cosmoCoeff_neg] using flatLCDM_coeffs Ω _ t₀ hL hs.neg

theorem flatLCDM_coeffs_p1_3 : dropped% Checked.Cosmography.Aviles.flatLCDM_coeffs 1 3 := by
  intro Ω a t₀ hs h
  exact flatLCDM_coeffs Ω a t₀ (lcdm_noDiff h) hs

theorem flatCPL_coeffs_p1_2 : dropped% Checked.Cosmography.CPL.flatCPL_coeffs 1 2 := by
  intro Ω w₀ wₐ a t₀ hs h
  rcases cpl_noPos h with hL | hL
  · exact CPL.flatCPL_coeffs Ω w₀ wₐ a t₀ hL hs
  · simpa only [decel_neg, cosmoCoeff_neg] using CPL.flatCPL_coeffs Ω w₀ wₐ _ t₀ hL hs.neg

theorem flatCPL_coeffs_p1_3 : dropped% Checked.Cosmography.CPL.flatCPL_coeffs 1 3 := by
  intro Ω w₀ wₐ a t₀ hs h
  exact CPL.flatCPL_coeffs Ω w₀ wₐ a t₀ (cpl_noDiff h) hs

theorem printedL0_ne_p1_2 : dropped% Checked.Cosmography.CPL.printedL0_ne 1 2 := by
  intro Ω w₀ wₐ a t₀ hs hne h
  rcases cpl_noPos h with hL | hL
  · exact CPL.printedL0_ne Ω w₀ wₐ a t₀ hL hs hne
  · simpa only [cosmoCoeff_neg] using CPL.printedL0_ne Ω w₀ wₐ _ t₀ hL hs.neg hne

theorem printedL0_ne_p1_3 : dropped% Checked.Cosmography.CPL.printedL0_ne 1 3 := by
  intro Ω w₀ wₐ a t₀ hs hne h
  exact CPL.printedL0_ne Ω w₀ wₐ a t₀ (cpl_noDiff h) hs hne

theorem F1_l0_p1_2 : dropped% Checked.Records.F1_l0 1 2 := by
  intro a t₀ hs h
  rcases lcdm_noPos h with hL | hL
  · exact F1_l0 a t₀ hL hs
  · simpa only [cosmoCoeff_neg] using F1_l0 _ t₀ hL hs.neg

theorem F1_l0_p1_3 : dropped% Checked.Records.F1_l0 1 3 := by
  intro a t₀ hs h
  exact F1_l0 a t₀ (lcdm_noDiff h) hs

theorem F2_toy_p1_2 : dropped% Checked.Records.F2_toy 1 2 := by
  intro a t₀ hs h
  rcases cpl_noPos h with hL | hL
  · exact F2_toy a t₀ hL hs
  · simpa only [cosmoCoeff_neg] using F2_toy _ t₀ hL hs.neg

theorem F2_toy_p1_3 : dropped% Checked.Records.F2_toy 1 3 := by
  intro a t₀ hs h
  exact F2_toy a t₀ (cpl_noDiff h) hs

theorem F2_error_p1_2 : dropped% Checked.Records.F2_error 1 2 := by
  intro w₀ a t₀ hs h
  rcases cpl_noPos h with hL | hL
  · exact F2_error w₀ a t₀ hL hs
  · simpa only [cosmoCoeff_neg] using F2_error w₀ _ t₀ hL hs.neg

theorem F2_error_p1_3 : dropped% Checked.Records.F2_error 1 3 := by
  intro w₀ a t₀ hs h
  exact F2_error w₀ a t₀ (cpl_noDiff h) hs

theorem F3_D4_LCDM_p1_2 : dropped% Checked.Records.F3_D4_LCDM 1 2 := by
  intro a t₀ hs h
  rcases lcdm_noPos h with hL | hL
  · exact F3_D4_LCDM a t₀ hL hs
  · simpa only [decel_neg, cosmoCoeff_neg] using F3_D4_LCDM _ t₀ hL hs.neg

theorem F3_D4_LCDM_p1_3 : dropped% Checked.Records.F3_D4_LCDM 1 3 := by
  intro a t₀ hs h
  exact F3_D4_LCDM a t₀ (lcdm_noDiff h) hs

/-- `0 < H₀` is needed in flat ΛCDM's coefficients: the static model's third coefficient is 0, not 1. -/
theorem flatLCDM_coeffs_p1_1 : necessity% Checked.Cosmography.Aviles.flatLCDM_coeffs 1 1 := by
  refine ⟨0, fun _ => 1, 0, contDiffAt_const, st_law _ _, ?_⟩
  rintro ⟨-, h, -⟩; rw [st_coeff 3 (by norm_num)] at h; norm_num at h

/-- The ΛCDM law is needed: de Sitter (H₀ = 1 > 0) has deceleration −1, not 1/2 at Ω = 1. -/
theorem flatLCDM_coeffs_p1_4 : necessity% Checked.Cosmography.Aviles.flatLCDM_coeffs 1 2 := by
  refine ⟨1, Real.exp, 0, dS_smooth _, dS_H_pos, dS_ev, ?_⟩
  rintro ⟨h, -⟩; rw [dS_decel] at h; norm_num at h

/-- `0 < H₀` is needed in flat CPL's coefficients: static third coefficient 0, claimed 1 at Ω = 1. -/
theorem flatCPL_coeffs_p1_1 : necessity% Checked.Cosmography.CPL.flatCPL_coeffs 1 1 := by
  refine ⟨1, 0, 0, fun _ => 1, 0, contDiffAt_const, st_law _ _, ?_⟩
  rintro ⟨-, h, -⟩; rw [st_coeff 3 (by norm_num)] at h; norm_num at h

/-- The CPL law is needed: de Sitter has deceleration −1, not 1/2 at Ω = 1. -/
theorem flatCPL_coeffs_p1_4 : necessity% Checked.Cosmography.CPL.flatCPL_coeffs 1 2 := by
  refine ⟨1, 0, 0, Real.exp, 0, dS_smooth _, dS_H_pos, dS_ev, ?_⟩
  rintro ⟨h, -⟩; rw [dS_decel] at h; norm_num at h

/-- `0 < H₀` is needed in the misprint statement: the static fifth coefficient 0 equals the printed
formula at Ω = 0, w₀ = 0, wₐ = (−213 + √43409)/14 (a root of 7wₐ² + 213wₐ + 70 = 0, so the printed value
35/2 + (213 + 7wₐ)wₐ/4 is 0), where (1 − Ω)(7 − Ω)wₐ = 7wₐ ≠ 0. -/
theorem printedL0_ne_p1_1 : necessity% Checked.Cosmography.CPL.printedL0_ne 1 1 := by
  set w := (-213 + √43409) / 14 with hw
  have hs : √43409 ^ 2 = 43409 := Real.sq_sqrt (by norm_num)
  have hq : 7 * w ^ 2 + 213 * w + 70 = 0 := by rw [hw]; nlinarith [hs]
  have hlt : √43409 < 213 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hpos : 0 < √43409 := Real.sqrt_pos.2 (by norm_num)
  have hw0 : w ≠ 0 := by rw [hw]; intro h; nlinarith
  refine ⟨0, 0, w, fun _ => 1, 0, contDiffAt_const, by
    simpa using hw0, st_law _ _, ?_⟩
  rw [st_coeff 5 (by norm_num)]
  intro h; apply h; linear_combination (-1 / 4 : ℝ) * hq

/-- The CPL law is needed in the misprint statement: de Sitter's fifth coefficient 1 equals the printed
formula at Ω = 0, w₀ = −1, wₐ = −96/7 (the hypothesis-level witness `printedL0_ne_h1`). -/
theorem printedL0_ne_p1_4 : necessity% Checked.Cosmography.CPL.printedL0_ne 1 2 := by
  refine ⟨0, -1, -96 / 7, Real.exp, 0, dS_smooth _, by norm_num, dS_H_pos, dS_ev, ?_⟩
  intro h; apply h; rw [dS_coeff]; norm_num

/-- Record F1: `0 < H₀` is needed (static fifth coefficient 0 does not round to 3.115). -/
theorem F1_l0_p1_1 : necessity% Checked.Records.F1_l0 1 1 := by
  refine ⟨fun _ => 1, 0, contDiffAt_const, st_law _ _, ?_⟩
  rw [st_coeff 5 (by norm_num)]; norm_num [RoundsTo, abs_le]

/-- Record F1: the ΛCDM law is needed (de Sitter's fifth coefficient 1 does not round to 3.115). -/
theorem F1_l0_p1_4 : necessity% Checked.Records.F1_l0 1 2 := by
  refine ⟨Real.exp, 0, dS_smooth _, dS_H_pos, dS_ev, ?_⟩
  rw [dS_coeff]; norm_num [RoundsTo, abs_le]

/-- Record F2 (toy): `0 < H₀` is needed (static fifth coefficient 0 does not round to 0.809). -/
theorem F2_toy_p1_1 : necessity% Checked.Records.F2_toy 1 1 := by
  refine ⟨fun _ => 1, 0, contDiffAt_const, st_law _ _, ?_⟩
  rintro ⟨h, -⟩; rw [st_coeff 5 (by norm_num)] at h; norm_num [RoundsTo, abs_le] at h

/-- Record F2 (toy): the CPL law is needed (de Sitter: 1 does not round to 0.809). -/
theorem F2_toy_p1_4 : necessity% Checked.Records.F2_toy 1 2 := by
  refine ⟨Real.exp, 0, dS_smooth _, dS_H_pos, dS_ev, ?_⟩
  rintro ⟨h, -⟩; rw [dS_coeff] at h; norm_num [RoundsTo, abs_le] at h

/-- Record F2 (error): `0 < H₀` is needed (static, w₀ = 0: 0 − printed ≈ 0.84, not 2.345). -/
theorem F2_error_p1_1 : necessity% Checked.Records.F2_error 1 1 := by
  refine ⟨0, fun _ => 1, 0, contDiffAt_const, st_law _ _, ?_⟩
  rw [st_coeff 5 (by norm_num)]; norm_num [RoundsTo, abs_le, printedCLSL0]

/-- Record F2 (error): the CPL law is needed (de Sitter, w₀ = 0: 1 − printed ≈ 1.84, not 2.345). -/
theorem F2_error_p1_4 : necessity% Checked.Records.F2_error 1 2 := by
  refine ⟨0, Real.exp, 0, dS_smooth _, dS_H_pos, dS_ev, ?_⟩
  rw [dS_coeff]; norm_num [RoundsTo, abs_le, printedCLSL0]

/-- Record F3: `0 < H₀` is needed (static: every coefficient 0, corrected D⁴ = 1, not 0.2153). -/
theorem F3_D4_LCDM_p1_1 : necessity% Checked.Records.F3_D4_LCDM 1 1 := by
  refine ⟨fun _ => 1, 0, contDiffAt_const, st_law _ _, ?_⟩
  rintro ⟨h, -⟩
  rw [st_decel, st_coeff 3 (by norm_num), st_coeff 4 (by norm_num), st_coeff 5 (by norm_num)] at h
  norm_num [RoundsTo, abs_le, Checked.Cosmography.CCS.correctD4] at h

/-- Record F3: the ΛCDM law is needed (de Sitter's corrected D⁴ is 1/5, not 0.2153). -/
theorem F3_D4_LCDM_p1_4 : necessity% Checked.Records.F3_D4_LCDM 1 2 := by
  refine ⟨Real.exp, 0, dS_smooth _, dS_H_pos, dS_ev, ?_⟩
  rintro ⟨h, -⟩
  rw [dS_decel, dS_coeff, dS_coeff, dS_coeff] at h
  norm_num [RoundsTo, abs_le, Checked.Cosmography.CCS.correctD4] at h

end Cosmography

section Chemistry
open Checked.Records Checked.Chemistry.CubicEOS

/-- vdW: zero slope is needed: at T = 3/16 the curvature vanishes, the slope is 1/16, and Z = −2/3. -/
theorem vdW_constants_p4_1 : necessity% Checked.Chemistry.CubicEOS.vdW_constants 4 1 := by
  refine ⟨1, 1, 1, 3 / 16, 2, one_pos, one_pos, by norm_num, ?_, ?_⟩
  · rw [deriv2_P _ _ _ _ _ _ _ (by norm_num) (by norm_num)]; norm_num
  · rintro ⟨h, -⟩; norm_num [cubicP] at h

/-- vdW: zero curvature is needed: at T = 1/4 the slope vanishes and Z = 0. -/
theorem vdW_constants_p4_2 : necessity% Checked.Chemistry.CubicEOS.vdW_constants 4 2 := by
  refine ⟨1, 1, 1, 1 / 4, 2, one_pos, one_pos, by norm_num, ?_, ?_⟩
  · rw [(hasDerivAt_P _ _ _ _ _ _ _ (by norm_num) (by norm_num)).deriv]; norm_num
  · rintro ⟨h, -⟩; norm_num [cubicP] at h

/-- RK: zero slope is needed: at T = 19/216 the curvature vanishes and Z = −34/19. -/
theorem rk_constants_p4_1 : necessity% Checked.Chemistry.CubicEOS.rk_constants 4 1 := by
  refine ⟨1, 1, 1, 19 / 216, 2, one_pos, one_pos, by norm_num, ?_, ?_⟩
  · rw [deriv2_P _ _ _ _ _ _ _ (by norm_num) (by norm_num)]; norm_num
  · rintro ⟨h, -⟩; norm_num [cubicP] at h

/-- RK: zero curvature is needed: at T = 5/36 the slope vanishes and Z = −2/5. -/
theorem rk_constants_p4_2 : necessity% Checked.Chemistry.CubicEOS.rk_constants 4 2 := by
  refine ⟨1, 1, 1, 5 / 36, 2, one_pos, one_pos, by norm_num, ?_, ?_⟩
  · rw [(hasDerivAt_P _ _ _ _ _ _ _ (by norm_num) (by norm_num)).deriv]; norm_num
  · rintro ⟨h, -⟩; norm_num [cubicP] at h

/-- PR: zero slope is needed: at T = 29/343 the curvature vanishes and Z = −40/29. -/
theorem pr_constants_p4_1 : necessity% Checked.Chemistry.CubicEOS.pr_constants 4 1 := by
  refine ⟨1, 1, 1, 29 / 343, 2, one_pos, one_pos, by norm_num, ?_, ?_⟩
  · rw [deriv2_P _ _ _ _ _ _ _ (by norm_num) (by norm_num)]; norm_num
  · rintro ⟨h, -⟩; norm_num [cubicP, RoundsTo, abs_le] at h

/-- PR: zero curvature is needed: at T = 6/49 the slope vanishes and Z = −1/3. -/
theorem pr_constants_p4_2 : necessity% Checked.Chemistry.CubicEOS.pr_constants 4 2 := by
  refine ⟨1, 1, 1, 6 / 49, 2, one_pos, one_pos, by norm_num, ?_, ?_⟩
  · rw [(hasDerivAt_P _ _ _ _ _ _ _ (by norm_num) (by norm_num)).deriv]; norm_num
  · rintro ⟨h, -⟩; norm_num [cubicP, RoundsTo, abs_le] at h

end Chemistry

section Duffing
open Checked.Sim.Duffing

/-- Duffing: the initial position is needed: the rest state x ≡ 0 solves the equation with v(0) = 0. -/
theorem duffing_first_zero_sol_p1_1 : necessity% Checked.Sim.Duffing.duffing_first_zero_sol 1 1 := by
  refine ⟨fun _ => 0, ⟨fun _ => 0, rfl, fun t _ => ⟨?_, ?_⟩⟩, ?_⟩
  · exact hasDerivWithinAt_const _ _ _
  · simpa using hasDerivWithinAt_const t (Icc (0 : ℝ) (6 / 5)) (0 : ℝ)
  · rintro ⟨h, -⟩; exact lt_irrefl _ (h 0 (by norm_num))

/-- Duffing: the equation for the velocity is needed: x(t) = 1 − 2t², v(t) = −4t has x(0) = 1,
v(0) = 0, x' = v within the interval, and x(1) = −1 < 0. -/
theorem duffing_first_zero_sol_p1_4 : necessity% Checked.Sim.Duffing.duffing_first_zero_sol 1 4 := by
  refine ⟨fun t => 1 - 2 * t ^ 2, by norm_num, fun t => -4 * t, by norm_num, fun t _ => ?_, ?_⟩
  · have := ((hasDerivAt_pow 2 t).const_mul 2).const_sub 1
    convert this.hasDerivWithinAt using 1; push_cast; ring
  · rintro ⟨h, -⟩; have := h 1 (by norm_num); norm_num at this

end Duffing

end Checked.Trust.NCF
