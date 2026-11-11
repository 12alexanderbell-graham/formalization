import Checked.Trust.NonVacuity
import Checked.Cosmography.LookbackThird
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Checked.Math.LaneEmden
import Checked.Math.LaneEmden2
import Checked.Math.Gelfand
import Checked.Math.GelfandExists
import Checked.Math.GelfandPDE
import Checked.Math.GelfandPDEExists
import Checked.Townes.TownesShooting
import Checked.Blasius.Blasius
import Checked.Hiemenz.Hiemenz
import Checked.Hiemenz.HIVP
import Checked.Homann.Homann
import Checked.Homann.HmIVP
import Checked.Trust.Necessity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Checked.FalknerSkan.FalknerSkan
import Checked.Sim.Duffing
import Checked.Sim.MichaelisMenten
import Checked.Sim.Robertson
import Checked.Sim.RobLong
import Checked.Chemistry.CubicEOS
import Checked.Chemistry.Coexistence
import Checked.Chemistry.RKAcentric
import Checked.Chemistry.SRKAcentric
import Checked.Chemistry.PRAcentric
import Checked.Chemistry.PR78Acentric
import Checked.Trust.Witnesses
import Checked.Data.FR13
import Checked.Data.Moresco16
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.IntermediateValue
import Checked.Fidelity.FriedmannLCDM
import Checked.Fidelity.FriedmannCPL
import Checked.Fidelity.TransverseSpec
import Checked.Math.ThomasFermi
import Checked.Math.ThomasFermiExists
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Hypothesis necessity witnesses, second batch (trust track T2b, run 2026-11-09T2228Z)

Each theorem `<headline>_h<i>` proves `necessity% <headline> i`: data meeting every hypothesis of the
headline except the `i`-th, for which the headline's conclusion is false. Each theorem
`<headline>_r<i>` proves `dropped% <headline> i`: the headline holds without its `i`-th hypothesis.
`scripts/trust/StatementDeps.lean` matches these statements against the obligations it computes
from the headlines and reports the classification in `TRUST_MAP.md`.

Redundant hypotheses shown here:

* continuity of the derivative at a regular singular point (Lane–Emden indices 3 and 2, the
  Gelfand ball, the Townes undershoot and overshoot): it follows from the other hypotheses, by the
  generic `cont_at_zero` (for θ differentiable on [0, S] with derivative φ and
  φ' = −((m + 1)/ξ) φ + F with F bounded, the function ξ^(m+1) φ has a bounded derivative, so it
  tends to 0, so |φ(ξ)| ≤ M ξ and φ(0) = 0);
* the same for the Thomas–Fermi initial slope (`tf_cont`: φ is increasing and φ − 2K√x is
  decreasing near 0, and the slope of y at 0 lies within 2K√x of φ(x));
* the interval condition of the Gelfand ODE existence theorem (restrict a longer solution).

Needed hypotheses shown here (counterexamples):

* Gelfand ball: the interval length (the one-point interval), θ' = φ and the equation (w = 0 with
  φ = −s/3 or φ = 0);
* Blasius and the zero-gradient Falkner–Skan wall shear: the relation f' = p (a rational profile
  with q' = −K f q for f = −q'/(K q)) and the far-field condition (the zero solution);
* Hiemenz and Homann shooting bracket: the interval length (the one-point interval, on which every
  function has every derivative), f' = p (an explicit profile with p < 1 and q > 0), p' = q (the
  undershoot: p = 10η reaches 1 before q can turn negative; the overshoot: f = p = 0), the equation
  (an exponential profile), and the initial wall shear (the certified solution at the other end of
  the bracket does the opposite, by the companion headline);
* Thomas–Fermi: the initial value (the scaled solution 8 y(2x), from the existence theorem);
* the Gelfand PDE existence theorem: the upper bound on the eigenvalue (at λ = 4 the bound theorem
  rules out every solution);
* rigorous simulation headlines: the solution hypothesis (the zero functions);
* cubic equations of state (added in run 2026-11-11T0028Z): the positivity of the co-volume and the
  condition that the volume exceeds the co-volume, in the van der Waals, Redlich–Kwong and Peng–Robinson
  constants, and the volume and denominator conditions of the characterisation of critical points. At a
  pole of the isotherm (the co-volume itself, or a zero of the attraction denominator) the isotherm and its
  derivative are not differentiable, so Lean's junk derivatives are both zero and the critical-point
  condition holds there (`crit_of_unbounded`, `crit_at_b`, `crit_at_root`), while the claimed constants or
  the critical cubic fail;
* cosmography (added in run 2026-11-11T0028Z): the model laws of the flat ΛCDM and CPL coefficient
  theorems and of the records built on them (de Sitter meets every smoothness hypothesis and violates the
  claimed coefficients), and the condition on the matter density and the evolution parameter in the CPL
  misprint statements (where it fails, every flat CPL model has the printed coefficient);
* the lookback-time expansions (added in run 2026-11-11T0028Z): a nonzero present scale factor is
  redundant in Lean's total division (with a zero scale factor the redshift is −1 and the Hubble rate 0,
  so the remainder is t₀ − t, which is small), and a nonzero present velocity is needed (the scale factor
  1 + t² has redshift of order t², too small to absorb the remainder −t);
* the cosmographic series headlines that assume both a nonzero present scale factor and a nonzero
  Hubble rate (added in run 2026-11-11T0028Z): the first is redundant, since the Hubble rate is the
  velocity divided by the scale factor and division by zero gives zero (`ne_a0_of_hubble`); and a nonzero
  Hubble rate is needed for the misprint statement on the second luminosity-distance coefficient in y
  (the static model);
* the same series headlines (added in run 2026-11-11T0028Z): a nonzero Hubble rate is needed (the scale
  factor 1 + t² has zero velocity, so its remainder is minus the series itself, of the exact order of the
  redshift, not of higher order).
-/

open Set Filter Topology

namespace Checked.Trust.NCB

/-- Regular singular point, generic: if θ is differentiable on `[0, S]` with derivative φ and
φ' = −((m+1)/ξ) φ + F on `(0, S]` with F bounded, then φ is continuous at 0 (and φ(0) = 0). -/
theorem cont_at_zero (S : ℝ) (hS : 0 < S) (m : ℕ) (θ φ F : ℝ → ℝ) (M : ℝ)
    (h1 : ∀ ξ ∈ Icc 0 S, HasDerivWithinAt θ (φ ξ) (Icc 0 S) ξ)
    (h3 : ∀ ξ ∈ Ioc 0 S, HasDerivWithinAt φ (-(((m : ℝ) + 1) / ξ * φ ξ) + F ξ) (Icc 0 S) ξ)
    (hF : ∀ ξ ∈ Ioc 0 S, |F ξ| ≤ M) :
    ContinuousWithinAt φ (Icc 0 S) 0 := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hF S ⟨hS, le_rfl⟩)
  set g : ℝ → ℝ := fun ξ => ξ ^ (m + 1) * φ ξ with hg
  have hgd : ∀ ξ ∈ Ioc 0 S, HasDerivWithinAt g (ξ ^ (m + 1) * F ξ) (Icc 0 S) ξ := by
    intro ξ hξ
    have hξ0 : ξ ≠ 0 := hξ.1.ne'
    have h := ((hasDerivAt_pow (m + 1) ξ).hasDerivWithinAt (s := Icc 0 S)).mul (h3 ξ hξ)
    simp only [Nat.add_sub_cancel] at h
    convert h using 1
    rw [pow_succ]
    field_simp
    push_cast
    ring
  -- Lipschitz bound for g on [a, b] ⊆ (0, S]
  have hlip : ∀ a b, 0 < a → a ≤ b → b ≤ S → |g b - g a| ≤ M * b ^ (m + 1) * (b - a) := by
    intro a b ha hab hbS
    have hsub : Icc a b ⊆ Ioc 0 S := fun x hx => ⟨lt_of_lt_of_le ha hx.1, hx.2.trans hbS⟩
    have hsub' : Icc a b ⊆ Icc 0 S := Icc_subset_Icc ha.le hbS
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := g)
      (f' := fun ξ => ξ ^ (m + 1) * F ξ) (s := Icc a b) (C := M * b ^ (m + 1))
      (fun x hx => (hgd x (hsub hx)).mono hsub')
      (fun x hx => by
        have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
        rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hx0, mul_comm M]
        exact mul_le_mul (pow_le_pow_left₀ hx0.le hx.2 _) (hF x (hsub hx)) (abs_nonneg _)
          (pow_nonneg (hx0.le.trans hx.2) _))
      (convex_Icc a b) ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hab)] at h
  -- θ is Lipschitz at 0 (differentiability at 0)
  obtain ⟨δ, hδ, hθ0⟩ : ∃ δ > 0, ∀ x ∈ Icc 0 S, x < δ → |θ x - θ 0| ≤ (|φ 0| + 1) * x := by
    have h := ((h1 0 ⟨le_rfl, hS.le⟩).isLittleO.bound one_pos)
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
    obtain ⟨δ, hδ, hδ'⟩ := h
    refine ⟨δ, hδ, fun x hx hxδ => ?_⟩
    have hd : dist x 0 < δ := by rw [Real.dist_eq, sub_zero, abs_of_nonneg hx.1]; exact hxδ
    have := hδ' hd hx
    simp only [sub_zero, smul_eq_mul, Real.norm_eq_abs, one_mul, abs_of_nonneg hx.1] at this
    calc |θ x - θ 0| = |(θ x - θ 0 - x * φ 0) + x * φ 0| := by ring_nf
      _ ≤ |θ x - θ 0 - x * φ 0| + |x * φ 0| := abs_add_le _ _
      _ ≤ x + x * |φ 0| := by
          rw [abs_mul, abs_of_nonneg hx.1]; linarith
      _ = (|φ 0| + 1) * x := by ring
  set L := |φ 0| + 1 with hL
  have hL0 : 0 ≤ L := by positivity
  -- first bound: |g a| ≤ C a^(m+1) near 0
  set C := 2 ^ (m + 1) * (3 * L + M * S) with hC
  have hgC : ∀ a, 0 < a → 2 * a < δ → 2 * a ≤ S → |g a| ≤ C * a ^ (m + 1) := by
    intro a ha h2δ h2S
    have hlt : a < 2 * a := by linarith
    have hcont : ContinuousOn θ (Icc a (2 * a)) := fun x hx =>
      ((h1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩).continuousWithinAt).mono
        (Icc_subset_Icc ha.le h2S)
    have hder : ∀ x ∈ Ioo a (2 * a), HasDerivAt θ (φ x) x := fun x hx =>
      (h1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩).hasDerivAt
        (Icc_mem_nhds (by linarith [hx.1]) (by linarith [hx.2]))
    obtain ⟨ζ, hζ, hζeq⟩ := exists_hasDerivAt_eq_slope θ φ hlt hcont hder
    have hA := hθ0 (2 * a) ⟨by linarith, h2S⟩ h2δ
    have hB := hθ0 a ⟨ha.le, by linarith⟩ (by linarith)
    have hφζ : |φ ζ| ≤ 3 * L := by
      rw [hζeq, show 2 * a - a = a by ring, abs_div, abs_of_pos ha, div_le_iff₀ ha]
      calc |θ (2 * a) - θ a| = |(θ (2 * a) - θ 0) - (θ a - θ 0)| := by ring_nf
        _ ≤ |θ (2 * a) - θ 0| + |θ a - θ 0| := abs_sub _ _
        _ ≤ L * (2 * a) + L * a := add_le_add hA hB
        _ = 3 * L * a := by ring
    have hζ0 : 0 < ζ := ha.trans hζ.1
    have hgζ : |g ζ| ≤ (2 * a) ^ (m + 1) * (3 * L) := by
      simp only [hg, abs_mul, abs_pow, abs_of_pos hζ0]
      exact mul_le_mul (pow_le_pow_left₀ hζ0.le hζ.2.le _) hφζ (abs_nonneg _) (by positivity)
    have hl := hlip a ζ ha hζ.1.le (by linarith [hζ.2])
    have hl' : |g ζ - g a| ≤ M * (2 * a) ^ (m + 1) * a := by
      calc |g ζ - g a| ≤ M * ζ ^ (m + 1) * (ζ - a) := hl
        _ ≤ M * (2 * a) ^ (m + 1) * a := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hζ0.le hζ.2.le _) hM)
            (by linarith [hζ.2]) (by linarith [hζ.1]) (by positivity)
    have haS : a ≤ S := by linarith
    calc |g a| = |g ζ - (g ζ - g a)| := by ring_nf
      _ ≤ |g ζ| + |g ζ - g a| := abs_sub _ _
      _ ≤ (2 * a) ^ (m + 1) * (3 * L) + M * (2 * a) ^ (m + 1) * a := add_le_add hgζ hl'
      _ = 2 ^ (m + 1) * (3 * L + M * a) * a ^ (m + 1) := by ring
      _ ≤ C * a ^ (m + 1) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith
  -- refined bound: |g a| ≤ M a^(m+2) on (0, S]
  have hgM : ∀ a ∈ Ioc 0 S, |g a| ≤ M * a ^ (m + 1) * a := by
    intro a ha
    have hpos : 0 < min a (min (δ / 2) (S / 2)) := by
      have := ha.1; positivity
    have hlim : Tendsto (fun b : ℝ => M * a ^ (m + 1) * a + C * b ^ (m + 1)) (𝓝[>] 0)
        (𝓝 (M * a ^ (m + 1) * a + C * 0 ^ (m + 1))) :=
      ((continuous_const.add (continuous_const.mul (continuous_pow _))).tendsto 0).mono_left
        nhdsWithin_le_nhds
    simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
      zero_pow, mul_zero, add_zero] at hlim
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT hpos] with b hb
    have hb0 : 0 < b := hb.1
    have hba : b ≤ a := hb.2.le.trans (min_le_left _ _)
    have hbδ : 2 * b < δ := by
      have := hb.2.trans_le ((min_le_right _ _).trans (min_le_left _ _)); linarith
    have hbS : 2 * b ≤ S := by
      have := hb.2.le.trans ((min_le_right _ _).trans (min_le_right _ _)); linarith
    have h1' := hlip b a hb0 hba ha.2
    have h2' := hgC b hb0 hbδ hbS
    calc |g a| = |(g a - g b) + g b| := by ring_nf
      _ ≤ |g a - g b| + |g b| := abs_add_le _ _
      _ ≤ M * a ^ (m + 1) * (a - b) + C * b ^ (m + 1) := add_le_add h1' h2'
      _ ≤ M * a ^ (m + 1) * a + C * b ^ (m + 1) := by
          have : 0 ≤ M * a ^ (m + 1) * b := by have := ha.1; positivity
          nlinarith
  have hφM : ∀ a ∈ Ioc 0 S, |φ a| ≤ M * a := by
    intro a ha
    have hapos : 0 < a ^ (m + 1) := pow_pos ha.1 _
    have h := hgM a ha
    simp only [hg, abs_mul, abs_pow, abs_of_pos ha.1] at h
    nlinarith
  -- θ(x) − θ(0) = O(x²), so φ(0) = 0
  have hθ2 : ∀ x ∈ Icc 0 S, |θ x - θ 0| ≤ M * x ^ 2 := by
    intro x hx
    rcases hx.1.eq_or_lt with h0 | hx0
    · subst h0; simp
    have hcont : ContinuousOn θ (Icc 0 x) := fun y hy =>
      ((h1 y ⟨hy.1, hy.2.trans hx.2⟩).continuousWithinAt).mono (Icc_subset_Icc le_rfl hx.2)
    have hder : ∀ y ∈ Ioo 0 x, HasDerivAt θ (φ y) y := fun y hy =>
      (h1 y ⟨hy.1.le, hy.2.le.trans hx.2⟩).hasDerivAt
        (Icc_mem_nhds hy.1 (hy.2.trans_le hx.2))
    obtain ⟨ζ, hζ, hζeq⟩ := exists_hasDerivAt_eq_slope θ φ hx0 hcont hder
    have hb := hφM ζ ⟨hζ.1, hζ.2.le.trans hx.2⟩
    rw [hζeq, sub_zero, abs_div, abs_of_pos hx0, div_le_iff₀ hx0] at hb
    have hMx : M * ζ ≤ M * x := mul_le_mul_of_nonneg_left hζ.2.le hM
    nlinarith [mul_le_mul_of_nonneg_right hMx hx0.le]
  have h0 : HasDerivWithinAt θ 0 (Icc 0 S) 0 := by
    rw [hasDerivWithinAt_iff_isLittleO]
    simp only [sub_zero, smul_zero]
    have hO : (fun x => θ x - θ 0) =O[𝓝[Icc 0 S] 0] fun x : ℝ => x ^ 2 := by
      refine Asymptotics.IsBigO.of_bound M ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)]
      exact hθ2 x hx
    exact hO.trans_isLittleO ((Asymptotics.isLittleO_pow_id one_lt_two).mono nhdsWithin_le_nhds)
  have hφ0 : φ 0 = 0 :=
    (uniqueDiffOn_Icc hS 0 ⟨le_rfl, hS.le⟩).eq_deriv _ (h1 0 ⟨le_rfl, hS.le⟩) h0
  show Tendsto φ (𝓝[Icc 0 S] 0) (𝓝 (φ 0))
  rw [hφ0]
  have hlim : Tendsto (fun x : ℝ => M * x) (𝓝[Icc 0 S] 0) (𝓝 0) := by
    have := ((show Continuous fun x : ℝ => M * x by fun_prop).tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Icc 0 S))
    simpa using this
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [Real.norm_eq_abs]
  rcases hx.1.eq_or_lt with h0 | hx0
  · subst h0; simp [hφ0]
  · exact hφM x ⟨hx0, hx.2⟩

/-- Same as `cont_at_zero` with a right-hand side `G ∘ θ`, `G` continuous: the bound on `G ∘ θ`
comes from the continuity of θ on the compact interval. -/
theorem cont_at_zero_of_continuous (S : ℝ) (hS : 0 < S) (m : ℕ) (θ φ G : ℝ → ℝ)
    (hG : Continuous G)
    (h1 : ∀ ξ ∈ Icc 0 S, HasDerivWithinAt θ (φ ξ) (Icc 0 S) ξ)
    (h3 : ∀ ξ ∈ Ioc 0 S, HasDerivWithinAt φ (-(((m : ℝ) + 1) / ξ * φ ξ) + G (θ ξ)) (Icc 0 S) ξ) :
    ContinuousWithinAt φ (Icc 0 S) 0 := by
  have hθ : ContinuousOn θ (Icc 0 S) := fun x hx => (h1 x hx).continuousWithinAt
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hG.comp_continuousOn hθ)
  exact cont_at_zero S hS m θ φ (fun ξ => G (θ ξ)) M h1 h3
    (fun ξ hξ => by simpa [Real.norm_eq_abs] using hM ξ (Ioc_subset_Icc_self hξ))

/-! ### Redundant: continuity of φ at the regular singular point -/

theorem laneEmden3_constants_r2 : dropped% Checked.Math.LaneEmden.laneEmden3_constants 2 := by
  intro θ φ h1 h3 h4
  refine Checked.Math.LaneEmden.laneEmden3_constants θ φ h1 ?_ h3 h4
  exact cont_at_zero_of_continuous 7 (by norm_num) 1 θ φ (fun y => -y ^ 3) (by fun_prop) h1
    (fun ξ hξ => (h3 ξ hξ).congr_deriv (by push_cast; ring))

theorem laneEmden2_constants_r2 : dropped% Checked.Math.LaneEmden2.laneEmden2_constants 2 := by
  intro θ φ h1 h3 h4
  refine Checked.Math.LaneEmden2.laneEmden2_constants θ φ h1 ?_ h3 h4
  exact cont_at_zero_of_continuous 5 (by norm_num) 1 θ φ (fun y => -y ^ 2) (by fun_prop) h1
    (fun ξ hξ => (h3 ξ hξ).congr_deriv (by push_cast; ring))

theorem gelfand_ball_critical_r3 : dropped% Checked.Math.Gelfand.gelfand_ball_critical 3 := by
  intro S hS w φ h1 h3 h4
  refine Checked.Math.Gelfand.gelfand_ball_critical S hS w φ h1 ?_ h3 h4
  exact cont_at_zero_of_continuous S (by linarith) 1 w φ (fun y => -Real.exp y) (by fun_prop) h1
    (fun ξ hξ => (h3 ξ hξ).congr_deriv (by push_cast; ring))

theorem townes_under_r3 : dropped% Checked.Townes.Shooting.townes_under 3 := by
  intro S hS θ φ h1 h3 h4
  refine Checked.Townes.Shooting.townes_under S hS θ φ h1 ?_ h3 h4
  exact cont_at_zero_of_continuous S (by linarith) 0 θ φ (fun y => y - y ^ 3) (by fun_prop) h1
    (fun ξ hξ => (h3 ξ hξ).congr_deriv (by push_cast; ring))

theorem townes_over_r3 : dropped% Checked.Townes.Shooting.townes_over 3 := by
  intro S hS θ φ h1 h3 h4
  refine Checked.Townes.Shooting.townes_over S hS θ φ h1 ?_ h3 h4
  exact cont_at_zero_of_continuous S (by linarith) 0 θ φ (fun y => y - y ^ 3) (by fun_prop) h1
    (fun ξ hξ => (h3 ξ hξ).congr_deriv (by push_cast; ring))

/-! ### Gelfand ball: the interval length, θ' = φ and the equation are needed -/

theorem gelfand_ball_critical_h1 : necessity% Checked.Math.Gelfand.gelfand_ball_critical 1 := by
  refine ⟨0, fun _ => 0, fun _ => 0, fun s _ => hasDerivWithinAt_const _ _ _,
    continuousWithinAt_const, fun s hs => absurd hs (by simp), rfl, ?_⟩
  rintro ⟨s₁, h1, -, -, -, h5⟩
  simp only [Real.exp_zero, mul_one] at h5
  nlinarith

theorem gelfand_ball_critical_h4 : necessity% Checked.Math.Gelfand.gelfand_ball_critical 4 := by
  refine ⟨41 / 10, le_rfl, fun _ => 0, fun _ => 0, fun s _ => hasDerivWithinAt_const _ _ _,
    continuousWithinAt_const, rfl, ?_⟩
  rintro ⟨s₁, h1, -, -, -, h5⟩
  simp only [Real.exp_zero, mul_one] at h5
  nlinarith

theorem gelfand_ball_critical_h2 : necessity% Checked.Math.Gelfand.gelfand_ball_critical 2 := by
  refine ⟨41 / 10, le_rfl, fun _ => 0, fun s => -(s / 3), (continuous_id.div_const 3).neg.continuousWithinAt,
    fun s hs => ?_, rfl, ?_⟩
  · have hs0 : s ≠ 0 := (mem_Ioc.mp hs).1.ne'
    exact (((hasDerivAt_id' s).div_const 3).neg.hasDerivWithinAt).congr_deriv
      (by rw [Real.exp_zero]; field_simp; ring)
  · rintro ⟨s₁, h1, -, -, -, h5⟩
    simp only [Real.exp_zero, mul_one] at h5
    nlinarith

/-! ### Blasius: the relation f' = p and the far-field condition are needed -/

theorem blasius_wall_shear_h6 : necessity% Checked.Blasius.blasius_wall_shear 6 := by
  refine ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun η _ => hasDerivWithinAt_const _ _ _,
    fun η _ => hasDerivWithinAt_const _ _ _,
    fun η _ => (hasDerivWithinAt_const _ _ _).congr_deriv (by ring), rfl, rfl, ?_⟩
  rintro ⟨h, -⟩
  norm_num at h

/-- A rational profile with p(0) = 0, p → 1, q = p' > 0 on [0, ∞), q(0) = 1 and q'(0) = 0:
p = 1 − 1/D, q = (1 + 2η)/D², q' = −6η(1 + η)/D³ with D = 1 + η + η². Used with
f = −q'/(K q) for the equation q' = −K f q when the relation f' = p is dropped. -/
theorem ratProfile :
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun η : ℝ => 1 - (1 + η + η ^ 2)⁻¹)
      ((1 + 2 * η) / (1 + η + η ^ 2) ^ 2) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun η : ℝ => (1 + 2 * η) / (1 + η + η ^ 2) ^ 2)
      (-(6 * η * (1 + η)) / (1 + η + η ^ 2) ^ 3) (Ici 0) η) ∧
    Tendsto (fun η : ℝ => 1 - (1 + η + η ^ 2)⁻¹) atTop (𝓝 1) := by
  have hD : ∀ η : ℝ, 0 ≤ η → 0 < 1 + η + η ^ 2 := fun η hη => by positivity
  have hDd : ∀ η : ℝ, HasDerivAt (fun η : ℝ => 1 + η + η ^ 2) (1 + 2 * η) η := fun η => by
    have := ((hasDerivAt_id' η).const_add 1).add (hasDerivAt_pow 2 η)
    exact this.congr_deriv (by norm_num)
  refine ⟨fun η hη => ?_, fun η hη => ?_, ?_⟩
  · have h0 := hD η hη
    have := (hasDerivAt_const η (1 : ℝ)).sub ((hDd η).inv h0.ne')
    exact this.hasDerivWithinAt.congr_deriv (by field_simp; ring)
  · have h0 := hD η (mem_Ici.mp hη)
    have hn : HasDerivAt (fun η : ℝ => 1 + 2 * η) 2 η := by
      have := ((hasDerivAt_id' η).const_mul 2).const_add 1
      exact this.congr_deriv (by ring)
    have := hn.div ((hDd η).pow 2) (by exact (pow_pos h0 2).ne')
    refine this.hasDerivWithinAt.congr_deriv ?_
    simp only [Pi.pow_apply]
    field_simp
    ring
  · have hlim : Tendsto (fun η : ℝ => 1 + η + η ^ 2) atTop atTop := by
      refine tendsto_atTop_mono (fun η => ?_) (tendsto_atTop_add_const_left _ 1 tendsto_id)
      simp only [id]; nlinarith [sq_nonneg η]
    have := (tendsto_inv_atTop_zero.comp hlim).const_sub 1
    simpa using this

theorem blasius_wall_shear_h1 : necessity% Checked.Blasius.blasius_wall_shear 1 := by
  obtain ⟨h2, h3, h6⟩ := ratProfile
  refine ⟨fun η => 12 * η * (1 + η) / ((1 + 2 * η) * (1 + η + η ^ 2)),
    fun η => 1 - (1 + η + η ^ 2)⁻¹, fun η => (1 + 2 * η) / (1 + η + η ^ 2) ^ 2,
    h2, fun η hη => (h3 η hη).congr_deriv ?_, by norm_num, by norm_num, h6, ?_⟩
  · have h0 : 0 < 1 + η + η ^ 2 := by have := mem_Ici.mp hη; positivity
    have h1 : 0 < 1 + 2 * η := by have := mem_Ici.mp hη; linarith
    have h1' : 1 + η * 2 ≠ 0 := by linarith
    have h1'' : 1 + 2 * η ≠ 0 := by linarith
    field_simp
    ring
  · rintro ⟨-, h⟩
    norm_num at h

theorem fs_zero_wall_shear_h1 : necessity% Checked.FalknerSkan.fs_zero_wall_shear 1 := by
  obtain ⟨h2, h3, h6⟩ := ratProfile
  refine ⟨fun η => 6 * η * (1 + η) / ((1 + 2 * η) * (1 + η + η ^ 2)),
    fun η => 1 - (1 + η + η ^ 2)⁻¹, fun η => (1 + 2 * η) / (1 + η + η ^ 2) ^ 2,
    h2, fun η hη => (h3 η hη).congr_deriv ?_, by norm_num, by norm_num, h6, ?_⟩
  · have h0 : 0 < 1 + η + η ^ 2 := by have := mem_Ici.mp hη; positivity
    have h1 : 0 < 1 + 2 * η := by have := mem_Ici.mp hη; linarith
    have h1' : 1 + η * 2 ≠ 0 := by linarith
    have h1'' : 1 + 2 * η ≠ 0 := by linarith
    field_simp
  · rintro ⟨-, h⟩
    norm_num at h

theorem fs_zero_wall_shear_h6 : necessity% Checked.FalknerSkan.fs_zero_wall_shear 6 := by
  refine ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun η _ => hasDerivWithinAt_const _ _ _,
    fun η _ => hasDerivWithinAt_const _ _ _,
    fun η _ => (hasDerivWithinAt_const _ _ _).congr_deriv (by ring), rfl, rfl, ?_⟩
  rintro ⟨h, -⟩
  norm_num at h

/-- On the one-point interval `[0, 0]` every function has every derivative (within). -/
theorem hdw_point (f : ℝ → ℝ) (c x : ℝ) (hx : x ∈ Icc (0 : ℝ) 0) :
    HasDerivWithinAt f c (Icc 0 0) x := by
  obtain rfl : x = 0 := le_antisymm hx.2 hx.1
  rw [Icc_self, ← hasDerivWithinAt_sdiff_singleton, sdiff_self,
    hasDerivWithinAt_iff_isLittleO, nhdsWithin_empty]
  exact Asymptotics.isLittleO_bot _ _

/-- A profile for the shooting headlines when the relation f' = p is dropped:
q = Q e^{−4η}(1 + Bη) with B = 4 − 1/Q (so q(0) = Q, q'(0) = −1, q > 0), p = ∫₀^η q
(p < 1 when Q < 2), and f = (p² − 1 − q')/(K q), so that q' = −K f q − 1 + p² and f(0) = 0. -/
theorem shootProfile (K Q : ℝ) (hK : 0 < K) (hQ : 1 < Q) (hQ2 : Q < 2) :
    ∃ f p q : ℝ → ℝ, (∀ η, HasDerivAt p (q η) η) ∧
      (∀ η, 0 ≤ η → HasDerivAt q (-(K * f η * q η) - 1 + p η ^ 2) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ q 0 = Q ∧ (∀ η, 0 ≤ η → 0 < q η) ∧ (∀ η, 0 ≤ η → p η < 1) := by
  set B := 4 - 1 / Q with hB
  have hB0 : 0 < B := by
    rw [hB]; have : 1 / Q < 1 := by rw [div_lt_one (by linarith)]; exact hQ
    linarith
  have hEd : ∀ η : ℝ, HasDerivAt (fun η => Real.exp (-4 * η)) (-4 * Real.exp (-4 * η)) η :=
    fun η => ((hasDerivAt_id' η).const_mul (-4)).exp.congr_deriv (by ring)
  have hqpos : ∀ η : ℝ, 0 ≤ η → 0 < Q * Real.exp (-4 * η) * (1 + B * η) := fun η hη => by
    have := Real.exp_pos (-4 * η); have : 0 < 1 + B * η := by nlinarith
    have : 0 < Q := by linarith
    positivity
  refine ⟨fun η => ((Q * ((1 / 4 + B / 16) * (1 - Real.exp (-4 * η)) - B / 4 * η * Real.exp (-4 * η))) ^ 2
      - 1 - Q * Real.exp (-4 * η) * (B - 4 - 4 * B * η)) / (K * (Q * Real.exp (-4 * η) * (1 + B * η))),
    fun η => Q * ((1 / 4 + B / 16) * (1 - Real.exp (-4 * η)) - B / 4 * η * Real.exp (-4 * η)),
    fun η => Q * Real.exp (-4 * η) * (1 + B * η), fun η => ?_, fun η hη => ?_, ?_, by simp, by simp,
    hqpos, fun η hη => ?_⟩
  · have := ((((hasDerivAt_const η (1 : ℝ)).sub (hEd η)).const_mul (1 / 4 + B / 16)).sub
      ((((hasDerivAt_id' η).const_mul (B / 4)).mul (hEd η)))).const_mul Q
    refine this.congr_deriv ?_
    ring
  · have h0 := hqpos η hη
    have := (((hEd η).const_mul Q).mul (((hasDerivAt_id' η).const_mul B).const_add 1))
    refine this.congr_deriv ?_
    field_simp
    ring
  · have hBQ : B - 4 = -(1 / Q) := by rw [hB]; ring
    simp only [mul_zero, Real.exp_zero, sub_self, mul_one, add_zero, sub_zero]
    rw [hBQ]
    field_simp
    ring
  · have hE := Real.exp_pos (-4 * η)
    have hE1 : Real.exp (-4 * η) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hηE : 0 ≤ η * Real.exp (-4 * η) := by positivity
    have hQB : Q * (1 / 4 + B / 16) < 1 := by
      rw [hB]; have : Q * (1 / 4 + (4 - 1 / Q) / 16) = Q / 2 - 1 / 16 := by field_simp; ring
      rw [this]; linarith
    have h1 : (1 / 4 + B / 16) * (1 - Real.exp (-4 * η)) - B / 4 * η * Real.exp (-4 * η)
        ≤ 1 / 4 + B / 16 := by nlinarith
    calc Q * ((1 / 4 + B / 16) * (1 - Real.exp (-4 * η)) - B / 4 * η * Real.exp (-4 * η))
        ≤ Q * (1 / 4 + B / 16) := mul_le_mul_of_nonneg_left h1 (by linarith)
      _ < 1 := hQB

/-- A profile for the undershoot headlines when the relation p' = q is dropped: f = 5η²,
p = 10η (reaches 1 at η = 1/10) and q the solution of the linear equation
q' = −K f q − 1 + p² with q(0) = Q (integrating factor); q stays positive while p < 1. -/
theorem underProfile (K Q : ℝ) (hK : 0 < K) (hK2 : K ≤ 2) (hQ : 1 / 2 < Q) :
    ∃ q : ℝ → ℝ, (∀ η, HasDerivAt q (-(K * (5 * η ^ 2) * q η) - 1 + (10 * η) ^ 2) η) ∧
      q 0 = Q ∧ ∀ η, 0 ≤ η → η < 1 / 10 → 0 < q η := by
  have hφ : Continuous (fun s : ℝ => Real.exp (K * (5 * s ^ 3 / 3)) * ((10 * s) ^ 2 - 1)) := by
    fun_prop
  refine ⟨fun η => Real.exp (-(K * (5 * η ^ 3 / 3))) *
      (Q + ∫ s in (0 : ℝ)..η, Real.exp (K * (5 * s ^ 3 / 3)) * ((10 * s) ^ 2 - 1)),
    fun η => ?_, by simp, fun η hη0 hη1 => ?_⟩
  · have hI := (hφ.integral_hasStrictDerivAt 0 η).hasDerivAt
    have hF : HasDerivAt (fun η : ℝ => K * (5 * η ^ 3 / 3)) (K * (5 * η ^ 2)) η := by
      have := (((hasDerivAt_pow 3 η).const_mul 5).div_const 3).const_mul K
      exact this.congr_deriv (by push_cast; ring)
    have := hF.neg.exp.mul ((hasDerivAt_const η Q).add hI)
    refine this.congr_deriv ?_
    have h1 : Real.exp (-(K * (5 * η ^ 3 / 3))) * Real.exp (K * (5 * η ^ 3 / 3)) = 1 := by
      rw [← Real.exp_add]; simp
    simp only [Pi.neg_apply, Pi.add_apply]
    linear_combination ((10 * η) ^ 2 - 1) * h1
  · have hle : ∫ s in (0 : ℝ)..η, (-2 : ℝ) ≤
        ∫ s in (0 : ℝ)..η, Real.exp (K * (5 * s ^ 3 / 3)) * ((10 * s) ^ 2 - 1) := by
      refine intervalIntegral.integral_mono_on hη0 intervalIntegrable_const
        (hφ.intervalIntegrable _ _) (fun s hs => ?_)
      have hs1 : s < 1 / 10 := lt_of_le_of_lt hs.2 hη1
      have hs0 := hs.1
      have hx : K * (5 * s ^ 3 / 3) ≤ 1 / 2 := by
        have : s ^ 3 ≤ (1 / 10) ^ 3 := pow_le_pow_left₀ hs0 hs1.le 3
        nlinarith
      have he : Real.exp (K * (5 * s ^ 3 / 3)) ≤ 2 := by
        have h1 := Real.exp_le_exp.2 hx
        have h2 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
          rw [← Real.exp_add]; norm_num
        have h3 := Real.exp_one_lt_d9
        have h4 := Real.exp_pos (1 / 2)
        nlinarith
      have hp : 0 ≤ (10 * s) ^ 2 := sq_nonneg _
      have hE := Real.exp_pos (K * (5 * s ^ 3 / 3))
      nlinarith
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hle
    have := Real.exp_pos (-(K * (5 * η ^ 3 / 3)))
    have : 0 < Q + ∫ s in (0 : ℝ)..η, Real.exp (K * (5 * s ^ 3 / 3)) * ((10 * s) ^ 2 - 1) := by
      nlinarith
    positivity

/-! ### Hiemenz and Homann shooting bracket: interval length, f' = p, the equation and the wall shear are needed -/

theorem hiemenz_under_h1 : necessity% Checked.Hiemenz.hiemenz_under 1 := by
  refine ⟨0, fun _ => 0, fun _ => 0, fun _ => 1.2325876568, fun η hη => hdw_point _ _ _ hη,
    fun η hη => hdw_point _ _ _ hη, fun η hη => hdw_point _ _ _ hη, rfl, rfl, rfl, ?_⟩
  rintro ⟨η, -, h, -⟩
  norm_num at h

theorem hiemenz_over_h1 : necessity% Checked.Hiemenz.hiemenz_over 1 := by
  refine ⟨0, fun _ => 0, fun _ => 0, fun _ => 1.2325876569, fun η hη => hdw_point _ _ _ hη,
    fun η hη => hdw_point _ _ _ hη, fun η hη => hdw_point _ _ _ hη, rfl, rfl, rfl, ?_⟩
  rintro ⟨η, -, h, -⟩
  norm_num at h

theorem hiemenz_under_h2 : necessity% Checked.Hiemenz.hiemenz_under 2 := by
  obtain ⟨f, p, q, hp, hq, hf0, hp0, hq0, hqpos, -⟩ :=
    shootProfile 1 1.2325876568 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨15 / 2, le_rfl, f, p, q, fun η _ => (hp η).hasDerivWithinAt,
    fun η hη => ((hq η hη.1).congr_deriv (by ring)).hasDerivWithinAt, hf0, hp0, hq0, ?_⟩
  rintro ⟨η, hη, h, -⟩
  exact absurd h (not_lt.2 (hqpos η hη.1.le).le)

theorem hiemenz_over_h2 : necessity% Checked.Hiemenz.hiemenz_over 2 := by
  obtain ⟨f, p, q, hp, hq, hf0, hp0, hq0, -, hp1⟩ :=
    shootProfile 1 1.2325876569 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨15 / 2, le_rfl, f, p, q, fun η _ => (hp η).hasDerivWithinAt,
    fun η hη => ((hq η hη.1).congr_deriv (by ring)).hasDerivWithinAt, hf0, hp0, hq0, ?_⟩
  rintro ⟨η, hη, h, -⟩
  linarith [hp1 η hη.1.le]

theorem hiemenz_over_h3 : necessity% Checked.Hiemenz.hiemenz_over 3 := by
  refine ⟨15 / 2, le_rfl, fun _ => 0, fun _ => 0, fun η => 1.2325876569 - η,
    fun η _ => hasDerivWithinAt_const _ _ _,
    fun η _ => (((hasDerivAt_const η (1.2325876569 : ℝ)).sub (hasDerivAt_id' η)).hasDerivWithinAt).congr_deriv
      (by ring), rfl, rfl, by norm_num, ?_⟩
  rintro ⟨η, -, h, -⟩
  norm_num at h

theorem hiemenz_under_h3 : necessity% Checked.Hiemenz.hiemenz_under 3 := by
  obtain ⟨q, hq, hq0, hqpos⟩ := underProfile 1 1.2325876568 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨15 / 2, le_rfl, fun η => 5 * η ^ 2, fun η => 10 * η, q, fun η _ => ?_,
    fun η _ => ((hq η).congr_deriv (by ring)).hasDerivWithinAt, by norm_num, by norm_num, hq0, ?_⟩
  · exact (((hasDerivAt_pow 2 η).const_mul 5).hasDerivWithinAt).congr_deriv (by push_cast; ring)
  · rintro ⟨η, hη, hneg, hp⟩
    have h1 := hp η ⟨hη.1.le, le_rfl⟩
    exact absurd hneg (not_lt.2 (hqpos η hη.1.le (by linarith)).le)

theorem hiemenz_under_h4 : necessity% Checked.Hiemenz.hiemenz_under 4 := by
  obtain ⟨h1, h2, -, -, -⟩ := Checked.Trust.NC.expProfile 1.2325876568 (by norm_num)
  refine ⟨15 / 2, le_rfl, fun η => η - (1 - Real.exp (-1.2325876568 * η)) / 1.2325876568, fun η => 1 - Real.exp (-1.2325876568 * η),
    fun η => 1.2325876568 * Real.exp (-1.2325876568 * η), fun η hη => (h1 η (mem_Ici.2 hη.1)).mono Icc_subset_Ici_self,
    fun η hη => (h2 η (mem_Ici.2 hη.1)).mono Icc_subset_Ici_self, by simp, by simp, by simp, ?_⟩
  rintro ⟨η, -, h, -⟩
  exact absurd h (not_lt.2 (by positivity))

theorem hiemenz_over_h4 : necessity% Checked.Hiemenz.hiemenz_over 4 := by
  obtain ⟨h1, h2, -, -, -⟩ := Checked.Trust.NC.expProfile 1.2325876569 (by norm_num)
  refine ⟨15 / 2, le_rfl, fun η => η - (1 - Real.exp (-1.2325876569 * η)) / 1.2325876569, fun η => 1 - Real.exp (-1.2325876569 * η),
    fun η => 1.2325876569 * Real.exp (-1.2325876569 * η), fun η hη => (h1 η (mem_Ici.2 hη.1)).mono Icc_subset_Ici_self,
    fun η hη => (h2 η (mem_Ici.2 hη.1)).mono Icc_subset_Ici_self, by simp, by simp, by simp, ?_⟩
  rintro ⟨η, -, h, -⟩
  linarith [Real.exp_pos (-1.2325876569 * η)]

/-- The initial wall shear is needed: the certified solution with the other end of the bracket
overshoots, so it cannot undershoot. -/
theorem hiemenz_under_h7 : necessity% Checked.Hiemenz.hiemenz_under 7 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hq0⟩ := Checked.Hiemenz.HIVP.ivp_hi
  refine ⟨15 / 2, le_rfl, f, p, q, hf, hp, hq, hf0, hp0, ?_⟩
  obtain ⟨η, hη, hp1, hqpos⟩ := Checked.Hiemenz.hiemenz_over (15 / 2) le_rfl f p q hf hp hq hf0 hp0 hq0
  rintro ⟨η', hη', hq', hp'⟩
  rcases le_or_gt η' η with h | h
  · exact absurd hq' (not_lt.2 (hqpos η' ⟨hη'.1.le, h⟩).le)
  · exact absurd hp1 (not_lt.2 (hp' η ⟨hη.1.le, h.le⟩).le)

/-- The initial wall shear is needed: the certified solution with the other end of the bracket
undershoots, so it cannot overshoot. -/
theorem hiemenz_over_h7 : necessity% Checked.Hiemenz.hiemenz_over 7 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hq0⟩ := Checked.Hiemenz.HIVP.ivp_lo
  refine ⟨15 / 2, le_rfl, f, p, q, hf, hp, hq, hf0, hp0, ?_⟩
  obtain ⟨η, hη, hqneg, hp1⟩ := Checked.Hiemenz.hiemenz_under (15 / 2) le_rfl f p q hf hp hq hf0 hp0 hq0
  rintro ⟨η', hη', hp', hqpos⟩
  rcases le_or_gt η' η with h | h
  · exact absurd hp' (not_lt.2 (hp1 η' ⟨hη'.1.le, h⟩).le)
  · exact absurd hqneg (not_lt.2 (hqpos η ⟨hη.1.le, h.le⟩).le)

theorem homann_under_h1 : necessity% Checked.Homann.homann_under 1 := by
  refine ⟨0, fun _ => 0, fun _ => 0, fun _ => 1.3119376938, fun η hη => hdw_point _ _ _ hη,
    fun η hη => hdw_point _ _ _ hη, fun η hη => hdw_point _ _ _ hη, rfl, rfl, rfl, ?_⟩
  rintro ⟨η, -, h, -⟩
  norm_num at h

theorem homann_over_h1 : necessity% Checked.Homann.homann_over 1 := by
  refine ⟨0, fun _ => 0, fun _ => 0, fun _ => 1.3119376939, fun η hη => hdw_point _ _ _ hη,
    fun η hη => hdw_point _ _ _ hη, fun η hη => hdw_point _ _ _ hη, rfl, rfl, rfl, ?_⟩
  rintro ⟨η, -, h, -⟩
  norm_num at h

theorem homann_under_h2 : necessity% Checked.Homann.homann_under 2 := by
  obtain ⟨f, p, q, hp, hq, hf0, hp0, hq0, hqpos, -⟩ :=
    shootProfile 2 1.3119376938 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨6, le_rfl, f, p, q, fun η _ => (hp η).hasDerivWithinAt,
    fun η hη => ((hq η hη.1).congr_deriv (by ring)).hasDerivWithinAt, hf0, hp0, hq0, ?_⟩
  rintro ⟨η, hη, h, -⟩
  exact absurd h (not_lt.2 (hqpos η hη.1.le).le)

theorem homann_over_h2 : necessity% Checked.Homann.homann_over 2 := by
  obtain ⟨f, p, q, hp, hq, hf0, hp0, hq0, -, hp1⟩ :=
    shootProfile 2 1.3119376939 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨6, le_rfl, f, p, q, fun η _ => (hp η).hasDerivWithinAt,
    fun η hη => ((hq η hη.1).congr_deriv (by ring)).hasDerivWithinAt, hf0, hp0, hq0, ?_⟩
  rintro ⟨η, hη, h, -⟩
  linarith [hp1 η hη.1.le]

theorem homann_over_h3 : necessity% Checked.Homann.homann_over 3 := by
  refine ⟨6, le_rfl, fun _ => 0, fun _ => 0, fun η => 1.3119376939 - η,
    fun η _ => hasDerivWithinAt_const _ _ _,
    fun η _ => (((hasDerivAt_const η (1.3119376939 : ℝ)).sub (hasDerivAt_id' η)).hasDerivWithinAt).congr_deriv
      (by ring), rfl, rfl, by norm_num, ?_⟩
  rintro ⟨η, -, h, -⟩
  norm_num at h

theorem homann_under_h3 : necessity% Checked.Homann.homann_under 3 := by
  obtain ⟨q, hq, hq0, hqpos⟩ := underProfile 2 1.3119376938 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨6, le_rfl, fun η => 5 * η ^ 2, fun η => 10 * η, q, fun η _ => ?_,
    fun η _ => ((hq η).congr_deriv (by ring)).hasDerivWithinAt, by norm_num, by norm_num, hq0, ?_⟩
  · exact (((hasDerivAt_pow 2 η).const_mul 5).hasDerivWithinAt).congr_deriv (by push_cast; ring)
  · rintro ⟨η, hη, hneg, hp⟩
    have h1 := hp η ⟨hη.1.le, le_rfl⟩
    exact absurd hneg (not_lt.2 (hqpos η hη.1.le (by linarith)).le)

theorem homann_under_h4 : necessity% Checked.Homann.homann_under 4 := by
  obtain ⟨h1, h2, -, -, -⟩ := Checked.Trust.NC.expProfile 1.3119376938 (by norm_num)
  refine ⟨6, le_rfl, fun η => η - (1 - Real.exp (-1.3119376938 * η)) / 1.3119376938, fun η => 1 - Real.exp (-1.3119376938 * η),
    fun η => 1.3119376938 * Real.exp (-1.3119376938 * η), fun η hη => (h1 η (mem_Ici.2 hη.1)).mono Icc_subset_Ici_self,
    fun η hη => (h2 η (mem_Ici.2 hη.1)).mono Icc_subset_Ici_self, by simp, by simp, by simp, ?_⟩
  rintro ⟨η, -, h, -⟩
  exact absurd h (not_lt.2 (by positivity))

theorem homann_over_h4 : necessity% Checked.Homann.homann_over 4 := by
  obtain ⟨h1, h2, -, -, -⟩ := Checked.Trust.NC.expProfile 1.3119376939 (by norm_num)
  refine ⟨6, le_rfl, fun η => η - (1 - Real.exp (-1.3119376939 * η)) / 1.3119376939, fun η => 1 - Real.exp (-1.3119376939 * η),
    fun η => 1.3119376939 * Real.exp (-1.3119376939 * η), fun η hη => (h1 η (mem_Ici.2 hη.1)).mono Icc_subset_Ici_self,
    fun η hη => (h2 η (mem_Ici.2 hη.1)).mono Icc_subset_Ici_self, by simp, by simp, by simp, ?_⟩
  rintro ⟨η, -, h, -⟩
  linarith [Real.exp_pos (-1.3119376939 * η)]

/-- The initial wall shear is needed: the certified solution with the other end of the bracket
overshoots, so it cannot undershoot. -/
theorem homann_under_h7 : necessity% Checked.Homann.homann_under 7 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hq0⟩ := Checked.Homann.HmIVP.ivp_hi
  refine ⟨6, le_rfl, f, p, q, hf, hp, hq, hf0, hp0, ?_⟩
  obtain ⟨η, hη, hp1, hqpos⟩ := Checked.Homann.homann_over 6 le_rfl f p q hf hp hq hf0 hp0 hq0
  rintro ⟨η', hη', hq', hp'⟩
  rcases le_or_gt η' η with h | h
  · exact absurd hq' (not_lt.2 (hqpos η' ⟨hη'.1.le, h⟩).le)
  · exact absurd hp1 (not_lt.2 (hp' η ⟨hη.1.le, h.le⟩).le)

/-- The initial wall shear is needed: the certified solution with the other end of the bracket
undershoots, so it cannot overshoot. -/
theorem homann_over_h7 : necessity% Checked.Homann.homann_over 7 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hq0⟩ := Checked.Homann.HmIVP.ivp_lo
  refine ⟨6, le_rfl, f, p, q, hf, hp, hq, hf0, hp0, ?_⟩
  obtain ⟨η, hη, hqneg, hp1⟩ := Checked.Homann.homann_under 6 le_rfl f p q hf hp hq hf0 hp0 hq0
  rintro ⟨η', hη', hp', hqpos⟩
  rcases le_or_gt η' η with h | h
  · exact absurd hp' (not_lt.2 (hp1 η' ⟨hη'.1.le, h⟩).le)
  · exact absurd hqneg (not_lt.2 (hqpos η ⟨hη.1.le, h.le⟩).le)

/-! ### Rigorous simulation headlines: the solution hypothesis is needed -/

theorem duffing_first_zero_sol_h1 : necessity% Checked.Sim.Duffing.duffing_first_zero_sol 1 := by
  refine ⟨fun _ => 0, ?_⟩
  rintro ⟨-, h⟩
  norm_num at h

theorem mm_half_conversion_h1 : necessity% Checked.Sim.MichaelisMenten.mm_half_conversion 1 := by
  refine ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, ?_⟩
  rintro ⟨-, h⟩
  norm_num at h

theorem rob_state40_h1 : necessity% Checked.Sim.Robertson.rob_state40 1 := by
  refine ⟨fun _ => 0, fun _ => 0, fun _ => 0, ?_⟩
  rintro ⟨h, -⟩
  norm_num at h

theorem rob_state1e11_h1 : necessity% Checked.Sim.RobLong.rob_state1e11 1 := by
  refine ⟨fun _ => 0, fun _ => 0, fun _ => 0, ?_⟩
  rintro ⟨h, -⟩
  norm_num at h

theorem rob_printed_y3_low_h1 : necessity% Checked.Sim.RobLong.rob_printed_y3_low 1 := by
  refine ⟨fun _ => 0, fun _ => 0, fun _ => 0, ?_⟩
  intro h
  norm_num at h

/-! ### Gelfand existence theorems -/

/-- The interval condition of the ODE existence theorem is redundant: a solution on a longer
interval restricts to any shorter one (and to the empty interval). -/
theorem exists_solution_r1 : dropped% Checked.Math.GelfandExists.exists_solution 1 := by
  intro S
  obtain ⟨w, φ, h1, h2, h3, h4⟩ :=
    Checked.Math.GelfandExists.exists_solution (max S (1 / 2)) (le_max_right _ _)
  have hsub : Icc (0 : ℝ) S ⊆ Icc 0 (max S (1 / 2)) := Icc_subset_Icc le_rfl (le_max_left _ _)
  refine ⟨w, φ, fun s hs => (h1 s (hsub hs)).mono hsub, h2.mono hsub, fun s hs => ?_, h4⟩
  exact (h3 s ⟨hs.1, hs.2.trans (le_max_left _ _)⟩).mono hsub

/-- The upper bound on the eigenvalue in the PDE existence theorem is needed: at λ = 4 there is no
solution, by the bound theorem. -/
theorem gelfand_pde_radial_exists_h2 :
    necessity% Checked.Math.GelfandPDEExists.gelfand_pde_radial_exists 2 := by
  refine ⟨4, by norm_num, ?_⟩
  rintro ⟨u, h1, h2, h3, h4, h5⟩
  have := Checked.Math.GelfandPDE.gelfand_pde_radial_bound 4 u h1 h2 h3 h4 h5
  norm_num at this

/-- Thomas–Fermi form: if y is differentiable on `[0, ∞)` with derivative φ, y > 0, and
φ' = y^{3/2}/√x for x > 0, then φ is right-continuous at 0. -/
theorem tf_cont (y φ : ℝ → ℝ)
    (hy : ∀ x, 0 ≤ x → HasDerivWithinAt y (φ x) (Ici 0) x)
    (hφ : ∀ x, 0 < x → HasDerivAt φ (y x ^ ((3 : ℝ) / 2) / Real.sqrt x) x)
    (hpos : ∀ x, 0 ≤ x → 0 < y x) :
    ContinuousWithinAt φ (Ici 0) 0 := by
  -- bound of y^{3/2} on [0, 1]
  have hyc : ContinuousOn y (Icc 0 1) := fun x hx =>
    ((hy x hx.1).continuousWithinAt).mono Icc_subset_Ici_self
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hyc
  set K := B ^ ((3 : ℝ) / 2) with hK
  have hK0 : 0 ≤ K := Real.rpow_nonneg (le_trans (norm_nonneg _) (hB 0 ⟨le_rfl, zero_le_one⟩)) _
  have hyK : ∀ x ∈ Icc (0 : ℝ) 1, y x ^ ((3 : ℝ) / 2) ≤ K := fun x hx => by
    have h := hB x hx
    rw [Real.norm_eq_abs, abs_of_pos (hpos x hx.1)] at h
    exact Real.rpow_le_rpow (hpos x hx.1).le h (by norm_num)
  -- φ is monotone on (0, ∞)
  have hmono : MonotoneOn φ (Ioi 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun x => y x ^ ((3 : ℝ) / 2) / Real.sqrt x) (convex_Ioi 0)
      (fun x hx => (hφ x hx).continuousAt.continuousWithinAt)
      (fun x hx => ?_) (fun x hx => ?_)
    · rw [interior_Ioi] at hx; exact (hφ x hx).hasDerivWithinAt
    · rw [interior_Ioi] at hx
      exact div_nonneg (Real.rpow_nonneg (hpos x (le_of_lt hx)).le _) (Real.sqrt_nonneg _)
  -- φ − 2K√x is antitone on (0, 1)
  have hanti : AntitoneOn (fun x => φ x - 2 * K * Real.sqrt x) (Ioo 0 1) := by
    have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun x => φ x - 2 * K * Real.sqrt x)
        (y x ^ ((3 : ℝ) / 2) / Real.sqrt x - 2 * K * (1 / (2 * Real.sqrt x))) x := fun x hx =>
      (hφ x hx.1).sub ((Real.hasDerivAt_sqrt hx.1.ne').const_mul _)
    refine antitoneOn_of_hasDerivWithinAt_nonpos
      (f' := fun x => y x ^ ((3 : ℝ) / 2) / Real.sqrt x - 2 * K * (1 / (2 * Real.sqrt x))) (convex_Ioo 0 1)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => ?_) (fun x hx => ?_)
    · rw [interior_Ioo] at hx; exact (hd x hx).hasDerivWithinAt
    · rw [interior_Ioo] at hx
      have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx.1
      have := hyK x ⟨hx.1.le, hx.2.le⟩
      rw [show 2 * K * (1 / (2 * Real.sqrt x)) = K / Real.sqrt x by field_simp, ← sub_div]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) hs.le
  -- the two-sided squeeze: for 0 < a ≤ b < 1, 0 ≤ φ b − φ a ≤ 2K√b
  have hsq : ∀ a b, 0 < a → a ≤ b → b < 1 → |φ b - φ a| ≤ 2 * K * Real.sqrt b := by
    intro a b ha hab hb1
    have h1 := hmono (mem_Ioi.2 ha) (mem_Ioi.2 (ha.trans_le hab)) hab
    have h2 := hanti ⟨ha, hab.trans_lt hb1⟩ ⟨ha.trans_le hab, hb1⟩ hab
    simp only at h2
    rw [abs_of_nonneg (sub_nonneg.2 h1)]
    have := Real.sqrt_nonneg a
    nlinarith
  -- slope of y at 0 tends to φ 0
  have hslope : Tendsto (fun x => (y x - y 0) / x) (𝓝[>] 0) (𝓝 (φ 0)) := by
    have h := (hasDerivWithinAt_iff_tendsto_slope.1 (hy 0 le_rfl))
    rw [show Ici (0 : ℝ) \ {0} = Ioi 0 by ext x; simp [lt_iff_le_and_ne, eq_comm]] at h
    refine h.congr (fun x => ?_)
    simp [slope_def_field]
  -- |φ x − slope x| ≤ 2K√x for 0 < x < 1 (mean value theorem)
  have hclose : ∀ x, 0 < x → x < 1 → |φ x - (y x - y 0) / x| ≤ 2 * K * Real.sqrt x := by
    intro x hx hx1
    have hcont : ContinuousOn y (Icc 0 x) := fun z hz =>
      ((hy z hz.1).continuousWithinAt).mono (fun w hw => (mem_Ici.2 hw.1))
    have hder : ∀ z ∈ Ioo 0 x, HasDerivAt y (φ z) z := fun z hz =>
      (hy z hz.1.le).hasDerivAt (Ici_mem_nhds hz.1)
    obtain ⟨ζ, hζ, hζeq⟩ := exists_hasDerivAt_eq_slope y φ hx hcont hder
    rw [sub_zero] at hζeq
    rw [← hζeq]
    exact hsq ζ x hζ.1 hζ.2.le hx1
  -- conclude
  rw [← Ioi_insert, continuousWithinAt_insert_self]
  show Tendsto φ (𝓝[>] 0) (𝓝 (φ 0))
  have hlim0 : Tendsto (fun x => 2 * K * Real.sqrt x) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun x => 2 * K * Real.sqrt x) (𝓝 0) (𝓝 (2 * K * Real.sqrt 0)) :=
      ((show Continuous fun x => 2 * K * Real.sqrt x by fun_prop).tendsto 0)
    simpa using this.mono_left nhdsWithin_le_nhds
  have hdiff : Tendsto (fun x => φ x - (y x - y 0) / x) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlim0
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    rw [Real.norm_eq_abs]
    exact hclose x hx.1 hx.2
  have := hdiff.add hslope
  simpa using this

/-- The equation is needed in the PDE bound: the zero function meets every other hypothesis, for
every eigenvalue, in particular λ = 4. -/
theorem gelfand_pde_radial_bound_h5 : necessity% Checked.Math.GelfandPDE.gelfand_pde_radial_bound 5 := by
  refine ⟨4, fun _ => 0, contDiffOn_const, continuousOn_const, fun _ _ => rfl,
    ⟨fun _ => 0, fun _ _ => rfl⟩, by norm_num⟩

/-! ### Pin theorems with a single hypothesis: the specification is needed

Without the specification any other object would be "pinned"; the negated predicate (or the
function plus one) is such an object. These witnesses are logically trivial; they are recorded so
that the classification of these pins is complete. -/

theorem ne_pred3 {α β γ : Type*} [Inhabited α] [Inhabited β] [Inhabited γ] (Q : α → β → γ → Prop) :
    ∃ P : α → β → γ → Prop, ¬ P = Q :=
  ⟨fun x y z => ¬ Q x y z, fun h => not_iff_self (Iff.of_eq (congrFun (congrFun (congrFun h
    default) default) default))⟩

theorem ne_pred5 {α β γ δ ε : Type*} [Inhabited α] [Inhabited β] [Inhabited γ] [Inhabited δ]
    [Inhabited ε] (Q : α → β → γ → δ → ε → Prop) :
    ∃ P : α → β → γ → δ → ε → Prop, ¬ P = Q :=
  ⟨fun x y z u v => ¬ Q x y z u v, fun h => not_iff_self (Iff.of_eq (congrFun (congrFun (congrFun
    (congrFun (congrFun h default) default) default) default) default))⟩

theorem flatLCDMSpec2_pins_h1 : necessity% Checked.Fidelity.flatLCDMSpec2_pins 1 := ne_pred3 _

theorem flatCPL_pins_h1 : necessity% Checked.Fidelity.flatCPL_pins 1 := ne_pred5 _

theorem transverseSpec_pins_h1 : necessity% Checked.Fidelity.transverseSpec_pins 1 := by
  refine ⟨fun K χ => Checked.Cosmography.Transverse.transverse K χ + 1, fun h => ?_⟩
  have := congrFun (congrFun h 0) 0
  linarith

/-! ### Farooq–Ratra 2013 best fit: the minimality hypothesis is needed (Ω = 0 is not the fit) -/

theorem fr13_bestfit68_h3 : necessity% Checked.Data.FR13.fr13_bestfit68 3 := by
  refine ⟨0, le_rfl, zero_le_one, ?_⟩
  rintro ⟨h, -⟩
  norm_num at h

theorem fr13_bestfit738_h3 : necessity% Checked.Data.FR13.fr13_bestfit738 3 := by
  refine ⟨0, le_rfl, zero_le_one, ?_⟩
  rintro ⟨h, -⟩
  norm_num at h

/-! ### Moresco et al. 2016 Table 5: the sample-size range and the AICc value are needed

For each model with k parameters the theorem says: if N lies in (k + 1, 31] and the printed AICc is
reproduced, to within the rounding of the printed value, by some maximum-likelihood term c, then
the printed BIC is not. Each hypothesis is needed: an N just outside the range (found by the intermediate value theorem on
k log N − 2k(k + 1)/(N − k − 1), with log 2 bounds at N = 1, 2, 32, 64) reproduces both printed
values exactly, and without the AICc condition c can be chosen to reproduce the BIC. -/

theorem log32 : Real.log 32 = 5 * Real.log 2 := by
  rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]; norm_num

theorem log64 : Real.log 64 = 6 * Real.log 2 := by
  rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; norm_num

theorem table5_oL_inconsistent_h2 : necessity% Checked.Data.Moresco16.table5_oL_inconsistent 2 := by
  have hc : ContinuousOn (fun N : ℝ => 3 * Real.log N - 2 * 3 * (3 + 1) / (N - 3 - 1)) (Icc 32 64) := by
    refine ContinuousOn.sub (continuousOn_const.mul (Real.continuousOn_log.mono ?_))
      (continuousOn_const.div (by fun_prop) ?_)
    · intro x hx; simp only [mem_compl_iff, mem_singleton_iff]; exact ne_of_gt (by linarith [hx.1])
    · intro x hx; exact ne_of_gt (by linarith [hx.1])
  have t1 := Real.log_two_gt_d9
  have t2 := Real.log_two_lt_d9
  have ha : (fun N : ℝ => 3 * Real.log N - 2 * 3 * (3 + 1) / (N - 3 - 1)) 32 ≤ (25.71 - 21.41 + 2 * 3) := by
    simp only []; rw [log32]; norm_num; linarith
  have hb : (25.71 - 21.41 + 2 * 3) ≤ (fun N : ℝ => 3 * Real.log N - 2 * 3 * (3 + 1) / (N - 3 - 1)) 64 := by
    simp only []; rw [log64]; norm_num; linarith
  obtain ⟨N, hN, hgN⟩ := intermediate_value_Icc (by norm_num) hc ⟨ha, hb⟩
  simp only [] at hgN
  refine ⟨N, 25.71 - 3 * Real.log N, ?_, ?_, ?_⟩
  · linarith [hN.1]
  · rw [show 25.71 - 3 * Real.log N + 2 * 3 + 2 * 3 * (3 + 1) / (N - 3 - 1) - 21.41 = 0 by linarith]
    norm_num
  · rw [show 25.71 - 3 * Real.log N + 3 * Real.log N - 25.71 = 0 by ring]
    norm_num

theorem table5_oL_inconsistent_h1 : necessity% Checked.Data.Moresco16.table5_oL_inconsistent 1 := by
  have hc : ContinuousOn (fun N : ℝ => 3 * Real.log N - 2 * 3 * (3 + 1) / (N - 3 - 1)) (Icc 1 2) := by
    refine ContinuousOn.sub (continuousOn_const.mul (Real.continuousOn_log.mono ?_))
      (continuousOn_const.div (by fun_prop) ?_)
    · intro x hx; simp only [mem_compl_iff, mem_singleton_iff]; exact ne_of_gt (by linarith [hx.1])
    · intro x hx; exact ne_of_lt (by linarith [hx.2])
  have t1 := Real.log_two_gt_d9
  have t2 := Real.log_two_lt_d9
  have ha : (fun N : ℝ => 3 * Real.log N - 2 * 3 * (3 + 1) / (N - 3 - 1)) 1 ≤ (25.71 - 21.41 + 2 * 3) := by
    simp only []; rw [Real.log_one]; norm_num
  have hb : (25.71 - 21.41 + 2 * 3) ≤ (fun N : ℝ => 3 * Real.log N - 2 * 3 * (3 + 1) / (N - 3 - 1)) 2 := by
    simp only []; norm_num; linarith
  obtain ⟨N, hN, hgN⟩ := intermediate_value_Icc (by norm_num) hc ⟨ha, hb⟩
  simp only [] at hgN
  refine ⟨N, 25.71 - 3 * Real.log N, ?_, ?_, ?_⟩
  · linarith [hN.2]
  · rw [show 25.71 - 3 * Real.log N + 2 * 3 + 2 * 3 * (3 + 1) / (N - 3 - 1) - 21.41 = 0 by linarith]
    norm_num
  · rw [show 25.71 - 3 * Real.log N + 3 * Real.log N - 25.71 = 0 by ring]
    norm_num

theorem table5_oL_inconsistent_h3 : necessity% Checked.Data.Moresco16.table5_oL_inconsistent 3 := by
  refine ⟨10, 25.71 - 3 * Real.log 10, by norm_num, by norm_num, ?_⟩
  rw [show 25.71 - 3 * Real.log 10 + 3 * Real.log 10 - 25.71 = 0 by ring]
  norm_num

theorem table5_pw_inconsistent_h2 : necessity% Checked.Data.Moresco16.table5_pw_inconsistent 2 := by
  have hc : ContinuousOn (fun N : ℝ => 4 * Real.log N - 2 * 4 * (4 + 1) / (N - 4 - 1)) (Icc 32 64) := by
    refine ContinuousOn.sub (continuousOn_const.mul (Real.continuousOn_log.mono ?_))
      (continuousOn_const.div (by fun_prop) ?_)
    · intro x hx; simp only [mem_compl_iff, mem_singleton_iff]; exact ne_of_gt (by linarith [hx.1])
    · intro x hx; exact ne_of_gt (by linarith [hx.1])
  have t1 := Real.log_two_gt_d9
  have t2 := Real.log_two_lt_d9
  have ha : (fun N : ℝ => 4 * Real.log N - 2 * 4 * (4 + 1) / (N - 4 - 1)) 32 ≤ (28.72 - 23.99 + 2 * 4) := by
    simp only []; rw [log32]; norm_num; linarith
  have hb : (28.72 - 23.99 + 2 * 4) ≤ (fun N : ℝ => 4 * Real.log N - 2 * 4 * (4 + 1) / (N - 4 - 1)) 64 := by
    simp only []; rw [log64]; norm_num; linarith
  obtain ⟨N, hN, hgN⟩ := intermediate_value_Icc (by norm_num) hc ⟨ha, hb⟩
  simp only [] at hgN
  refine ⟨N, 28.72 - 4 * Real.log N, ?_, ?_, ?_⟩
  · linarith [hN.1]
  · rw [show 28.72 - 4 * Real.log N + 2 * 4 + 2 * 4 * (4 + 1) / (N - 4 - 1) - 23.99 = 0 by linarith]
    norm_num
  · rw [show 28.72 - 4 * Real.log N + 4 * Real.log N - 28.72 = 0 by ring]
    norm_num

theorem table5_pw_inconsistent_h1 : necessity% Checked.Data.Moresco16.table5_pw_inconsistent 1 := by
  have hc : ContinuousOn (fun N : ℝ => 4 * Real.log N - 2 * 4 * (4 + 1) / (N - 4 - 1)) (Icc 1 2) := by
    refine ContinuousOn.sub (continuousOn_const.mul (Real.continuousOn_log.mono ?_))
      (continuousOn_const.div (by fun_prop) ?_)
    · intro x hx; simp only [mem_compl_iff, mem_singleton_iff]; exact ne_of_gt (by linarith [hx.1])
    · intro x hx; exact ne_of_lt (by linarith [hx.2])
  have t1 := Real.log_two_gt_d9
  have t2 := Real.log_two_lt_d9
  have ha : (fun N : ℝ => 4 * Real.log N - 2 * 4 * (4 + 1) / (N - 4 - 1)) 1 ≤ (28.72 - 23.99 + 2 * 4) := by
    simp only []; rw [Real.log_one]; norm_num
  have hb : (28.72 - 23.99 + 2 * 4) ≤ (fun N : ℝ => 4 * Real.log N - 2 * 4 * (4 + 1) / (N - 4 - 1)) 2 := by
    simp only []; norm_num; linarith
  obtain ⟨N, hN, hgN⟩ := intermediate_value_Icc (by norm_num) hc ⟨ha, hb⟩
  simp only [] at hgN
  refine ⟨N, 28.72 - 4 * Real.log N, ?_, ?_, ?_⟩
  · linarith [hN.2]
  · rw [show 28.72 - 4 * Real.log N + 2 * 4 + 2 * 4 * (4 + 1) / (N - 4 - 1) - 23.99 = 0 by linarith]
    norm_num
  · rw [show 28.72 - 4 * Real.log N + 4 * Real.log N - 28.72 = 0 by ring]
    norm_num

theorem table5_pw_inconsistent_h3 : necessity% Checked.Data.Moresco16.table5_pw_inconsistent 3 := by
  refine ⟨10, 28.72 - 4 * Real.log 10, by norm_num, by norm_num, ?_⟩
  rw [show 28.72 - 4 * Real.log 10 + 4 * Real.log 10 - 28.72 = 0 by ring]
  norm_num

theorem table5_line_inconsistent_h2 : necessity% Checked.Data.Moresco16.table5_line_inconsistent 2 := by
  have hc : ContinuousOn (fun N : ℝ => 2 * Real.log N - 2 * 2 * (2 + 1) / (N - 2 - 1)) (Icc 32 64) := by
    refine ContinuousOn.sub (continuousOn_const.mul (Real.continuousOn_log.mono ?_))
      (continuousOn_const.div (by fun_prop) ?_)
    · intro x hx; simp only [mem_compl_iff, mem_singleton_iff]; exact ne_of_gt (by linarith [hx.1])
    · intro x hx; exact ne_of_gt (by linarith [hx.1])
  have t1 := Real.log_two_gt_d9
  have t2 := Real.log_two_lt_d9
  have ha : (fun N : ℝ => 2 * Real.log N - 2 * 2 * (2 + 1) / (N - 2 - 1)) 32 ≤ (35.29 - 32.42 + 2 * 2) := by
    simp only []; rw [log32]; norm_num; linarith
  have hb : (35.29 - 32.42 + 2 * 2) ≤ (fun N : ℝ => 2 * Real.log N - 2 * 2 * (2 + 1) / (N - 2 - 1)) 64 := by
    simp only []; rw [log64]; norm_num; linarith
  obtain ⟨N, hN, hgN⟩ := intermediate_value_Icc (by norm_num) hc ⟨ha, hb⟩
  simp only [] at hgN
  refine ⟨N, 35.29 - 2 * Real.log N, ?_, ?_, ?_⟩
  · linarith [hN.1]
  · rw [show 35.29 - 2 * Real.log N + 2 * 2 + 2 * 2 * (2 + 1) / (N - 2 - 1) - 32.42 = 0 by linarith]
    norm_num
  · rw [show 35.29 - 2 * Real.log N + 2 * Real.log N - 35.29 = 0 by ring]
    norm_num

theorem table5_line_inconsistent_h1 : necessity% Checked.Data.Moresco16.table5_line_inconsistent 1 := by
  have hc : ContinuousOn (fun N : ℝ => 2 * Real.log N - 2 * 2 * (2 + 1) / (N - 2 - 1)) (Icc 1 2) := by
    refine ContinuousOn.sub (continuousOn_const.mul (Real.continuousOn_log.mono ?_))
      (continuousOn_const.div (by fun_prop) ?_)
    · intro x hx; simp only [mem_compl_iff, mem_singleton_iff]; exact ne_of_gt (by linarith [hx.1])
    · intro x hx; exact ne_of_lt (by linarith [hx.2])
  have t1 := Real.log_two_gt_d9
  have t2 := Real.log_two_lt_d9
  have ha : (fun N : ℝ => 2 * Real.log N - 2 * 2 * (2 + 1) / (N - 2 - 1)) 1 ≤ (35.29 - 32.42 + 2 * 2) := by
    simp only []; rw [Real.log_one]; norm_num
  have hb : (35.29 - 32.42 + 2 * 2) ≤ (fun N : ℝ => 2 * Real.log N - 2 * 2 * (2 + 1) / (N - 2 - 1)) 2 := by
    simp only []; norm_num; linarith
  obtain ⟨N, hN, hgN⟩ := intermediate_value_Icc (by norm_num) hc ⟨ha, hb⟩
  simp only [] at hgN
  refine ⟨N, 35.29 - 2 * Real.log N, ?_, ?_, ?_⟩
  · linarith [hN.2]
  · rw [show 35.29 - 2 * Real.log N + 2 * 2 + 2 * 2 * (2 + 1) / (N - 2 - 1) - 32.42 = 0 by linarith]
    norm_num
  · rw [show 35.29 - 2 * Real.log N + 2 * Real.log N - 35.29 = 0 by ring]
    norm_num

theorem table5_line_inconsistent_h3 : necessity% Checked.Data.Moresco16.table5_line_inconsistent 3 := by
  refine ⟨10, 35.29 - 2 * Real.log 10, by norm_num, by norm_num, ?_⟩
  rw [show 35.29 - 2 * Real.log 10 + 2 * Real.log 10 - 35.29 = 0 by ring]
  norm_num

/-! ### Thomas–Fermi: continuity of φ at 0 is redundant; the initial value is needed -/

theorem tf_initial_slope_r3 : dropped% Checked.Math.ThomasFermi.tf_initial_slope 3 := by
  intro y φ hy hφ h0 hpos hlim
  exact Checked.Math.ThomasFermi.tf_initial_slope y φ hy hφ (tf_cont y φ hy hφ hpos) h0 hpos hlim

/-- The initial value y(0) = 1 is needed: the scaled Thomas–Fermi solution 8·y(2x) (the equation
is invariant under y(x) ↦ λ³ y(λx)) meets every other hypothesis with initial slope 16·φ(0). -/
theorem tf_initial_slope_h4 : necessity% Checked.Math.ThomasFermi.tf_initial_slope 4 := by
  obtain ⟨y, φ, h1, h2, h3, h4, h5, h6⟩ := Checked.Math.ThomasFermiExists.tf_exists
  have hb := Checked.Math.ThomasFermi.tf_initial_slope y φ h1 h2 h3 h4 h5 h6
  have h8 : (8 : ℝ) ^ ((3 : ℝ) / 2) = 16 * Real.sqrt 2 := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one,
      ← Real.sqrt_eq_rpow, show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
    ring
  refine ⟨fun x => 8 * y (2 * x), fun x => 16 * φ (2 * x), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hc : HasDerivWithinAt (fun x : ℝ => 2 * x) 2 (Ici 0) x :=
      (((hasDerivAt_id x).const_mul 2).hasDerivWithinAt).congr_deriv (by simp)
    have := (h1 (2 * x) (by linarith)).comp x hc (fun z hz => by
      simp only [mem_Ici] at hz ⊢; linarith)
    exact (this.const_mul 8).congr_deriv (by ring)
  · intro x hx
    have hY := h5 (2 * x) (by linarith)
    have := ((h2 (2 * x) (by linarith)).comp x ((hasDerivAt_id x).const_mul 2)).const_mul 16
    refine this.congr_deriv ?_
    have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
    have h2s : 0 < Real.sqrt 2 := by positivity
    rw [Real.mul_rpow (by norm_num) hY.le, h8, Real.sqrt_mul (by norm_num)]
    field_simp
    rw [Real.sq_sqrt (by norm_num)]
  · have h3' : ContinuousWithinAt φ (Ici 0) (2 * 0) := by rwa [mul_zero]
    exact continuousWithinAt_const.mul (h3'.comp
      ((continuous_const.mul continuous_id).continuousWithinAt)
      (fun z hz => by simp only [mem_Ici, id] at hz ⊢; linarith))
  · intro x hx; have := h5 (2 * x) (by linarith); positivity
  · have := (h6.comp (tendsto_id.const_mul_atTop (show (0 : ℝ) < 2 by norm_num))).const_mul 8
    simpa using this
  · rintro ⟨h, -⟩
    simp only [mul_zero] at h
    linarith [hb.2]

/-! ### Cubic equations of state: the critical-point condition, a > 0 and the coexistence
condition are needed -/

section Chemistry
open Checked.Records Checked.Chemistry.CubicEOS Checked.Chemistry.Coexistence

/-- With a = 0 and T = 0 the isotherm is identically zero, so every volume is a critical point. -/
theorem zero_isotherm (R b u w : ℝ) : cubicP R 0 b u w 0 = fun _ => 0 := by
  funext x; simp [cubicP]

theorem zero_isotherm_critical (R b u w v : ℝ) : IsCriticalIsotherm (cubicP R 0 b u w 0) v := by
  rw [zero_isotherm R b u w]; simp [IsCriticalIsotherm]

theorem vdW_constants_h1 : necessity% Checked.Chemistry.CubicEOS.vdW_constants 1 := by
  refine ⟨1, 0, 1, 0, 2, one_pos, by norm_num, zero_isotherm_critical 1 1 0 0 2, ?_⟩
  rintro ⟨h, -⟩
  rw [zero_isotherm 1 1 0 0] at h
  norm_num at h

theorem vdW_constants_h4 : necessity% Checked.Chemistry.CubicEOS.vdW_constants 4 := by
  refine ⟨1, 1, 1, 1, 2, one_pos, one_pos, by norm_num, ?_⟩
  rintro ⟨h, -⟩
  norm_num [cubicP] at h

theorem rk_constants_h1 : necessity% Checked.Chemistry.CubicEOS.rk_constants 1 := by
  refine ⟨1, 0, 1, 0, 2, one_pos, by norm_num, zero_isotherm_critical 1 1 1 0 2, ?_⟩
  rintro ⟨h, -⟩
  rw [zero_isotherm 1 1 1 0] at h
  norm_num at h

theorem rk_constants_h4 : necessity% Checked.Chemistry.CubicEOS.rk_constants 4 := by
  refine ⟨1, 1, 1, 1, 2, one_pos, one_pos, by norm_num, ?_⟩
  rintro ⟨h, -⟩
  norm_num [cubicP] at h

theorem pr_constants_h1 : necessity% Checked.Chemistry.CubicEOS.pr_constants 1 := by
  refine ⟨1, 0, 1, 0, 2, one_pos, by norm_num, zero_isotherm_critical 1 1 2 (-1) 2, ?_⟩
  rintro ⟨h, -⟩
  rw [zero_isotherm 1 1 2 (-1)] at h
  norm_num [RoundsTo, abs_le] at h

theorem pr_constants_h4 : necessity% Checked.Chemistry.CubicEOS.pr_constants 4 := by
  refine ⟨1, 1, 1, 1, 2, one_pos, one_pos, by norm_num, ?_⟩
  rintro ⟨h, -⟩
  norm_num [cubicP, RoundsTo, abs_le] at h

/-- The positivity of the attraction parameter is needed in the characterisation of critical points:
with a = 0 and T = 0 every volume is critical, but the critical cubic need not vanish. -/
theorem isCritical_iff_h1 : necessity% Checked.Chemistry.CubicEOS.isCritical_iff 1 := by
  refine ⟨1, 0, 1, 0, 0, 0, 2, by norm_num, by norm_num, ?_⟩
  intro h
  have := (h.1 (zero_isotherm_critical 1 1 0 0 2)).1
  norm_num at this

/-- The coexistence hypothesis is needed: a saturation pressure 0 contradicts the conclusion. -/
theorem vdW_coexistence_unique_h5 : necessity% Checked.Chemistry.Coexistence.vdW_coexistence_unique 5 := by
  refine ⟨1, 1, 1, 2, 3, 0, one_pos, one_pos, one_pos, by norm_num, ?_⟩
  norm_num [RoundsTo, abs_le]

/-- With a = 0 the isotherm at 0.7 · 8a/(27Rb) = 0 is identically zero, so every coexistence state
has pressure 0 and the claimed pressure ratio fails. -/
theorem vdW_coexistence_exists_h2 : necessity% Checked.Chemistry.Coexistence.vdW_coexistence_exists 2 := by
  refine ⟨1, 0, 1, one_pos, one_pos, ?_⟩
  rintro ⟨vl, vg, ps, -, ⟨-, hpl, -, -⟩, h⟩
  have hz : cubicP 1 0 1 0 0 (7 / 10 * (8 * 0 / (27 * 1 * 1))) = fun _ => 0 := by
    funext x; simp [cubicP]
  rw [hz] at hpl
  subst hpl
  norm_num [RoundsTo, abs_le] at h

theorem rk_coexistence_unique_h8 : necessity% Checked.Chemistry.RKAcentric.rk_coexistence_unique 8 := by
  obtain ⟨Tc, vc, hT, hv, hc⟩ := Checked.Trust.NV.rk_crit_witness
  refine ⟨1, Real.sqrt Tc, 1, Tc, vc, 2, 3, 0, one_pos, Real.sqrt_pos.2 hT, one_pos, hT, hv, hc,
    by norm_num, ?_⟩
  rintro ⟨h, -⟩
  norm_num [RoundsTo, abs_le] at h

theorem srk_omega1_unique_h6 : necessity% Checked.Chemistry.SRKAcentric.srk_omega1_unique 6 := by
  obtain ⟨Tc, vc, -, hv, hc⟩ := Checked.Trust.NV.srk_crit_witness
  refine ⟨1, 1, 1, Tc, vc, 2, 3, 0, one_pos, one_pos, hv, hc, by norm_num, ?_⟩
  rintro ⟨h, -⟩
  norm_num [RoundsTo, abs_le] at h

theorem pr_omega1_unique_h6 : necessity% Checked.Chemistry.PRAcentric.pr_omega1_unique 6 := by
  obtain ⟨Tc, vc, -, hv, hc⟩ := Checked.Trust.NV.pr_crit_witness
  refine ⟨1, 1, 1, Tc, vc, 2, 3, 0, one_pos, one_pos, hv, hc, by norm_num, ?_⟩
  rintro ⟨h, -⟩
  norm_num [RoundsTo, abs_le] at h

theorem pr78_omega1_unique_h6 : necessity% Checked.Chemistry.PR78Acentric.pr78_omega1_unique 6 := by
  obtain ⟨Tc, vc, -, hv, hc⟩ := Checked.Trust.NV.pr_crit_witness
  refine ⟨1, 1, 1, Tc, vc, 2, 3, 0, one_pos, one_pos, hv, hc, by norm_num, ?_⟩
  rintro ⟨h, -⟩
  norm_num [RoundsTo, abs_le] at h

/-- With R = 0 (b = 1) the temperature 0.7 · 8a/(27Rb) is 0 in Lean's arithmetic and the isotherm is
−1/v², strictly increasing for v > 0: no two volumes have the same pressure, so no coexistence. -/
theorem vdW_coexistence_exists_h1 : necessity% Checked.Chemistry.Coexistence.vdW_coexistence_exists 1 := by
  refine ⟨0, 1, 1, one_pos, one_pos, ?_⟩
  rintro ⟨vl, vg, ps, hl, ⟨hlg, hpl, hpg, -⟩, -⟩
  simp only [cubicP] at hpl hpg
  have hvl : 0 < vl := by linarith
  have hvg : 0 < vg := by linarith
  simp at hpl hpg
  have e : (vl ^ 2)⁻¹ = (vg ^ 2)⁻¹ := by linarith
  have e2 := inv_inj.1 e
  nlinarith

/-- With b = 0 the temperature is 0 in Lean's arithmetic and the isotherm is −a/v² (a = 1), strictly
increasing for v > 0: no coexistence. -/
theorem vdW_coexistence_exists_h3 : necessity% Checked.Chemistry.Coexistence.vdW_coexistence_exists 3 := by
  refine ⟨1, 1, 0, one_pos, one_pos, ?_⟩
  rintro ⟨vl, vg, ps, hl, ⟨hlg, hpl, hpg, -⟩, -⟩
  simp only [cubicP] at hpl hpg
  have hvl : 0 < vl := by linarith
  have hvg : 0 < vg := by linarith
  simp at hpl hpg
  have e : (vl ^ 2)⁻¹ = (vg ^ 2)⁻¹ := by linarith
  have e2 := inv_inj.1 e
  nlinarith

/-- The sign of R is redundant in the coexistence-pressure theorem: for R ≠ 0 the isotherm at
0.7 · 8a/(27Rb) does not depend on R (R T = 0.7 · 8a/(27b)), and for R = 0 it is −a/v², which
admits no coexistence state with b < v_l. -/
theorem vdW_coexistence_unique_r1 : dropped% Checked.Chemistry.Coexistence.vdW_coexistence_unique 1 := by
  intro R a b vl vg ps ha hb hl h
  rcases eq_or_ne R 0 with hR | hR
  · subst hR
    exfalso
    obtain ⟨hlg, hpl, hpg, -⟩ := h
    simp only [cubicP] at hpl hpg
    have hvl : 0 < vl := by linarith
    have hvg : 0 < vg := by linarith
    have e : a / (vl ^ 2 + 0 * b * vl + 0 * b ^ 2) = a / (vg ^ 2 + 0 * b * vg + 0 * b ^ 2) := by
      simp at hpl hpg ⊢; linarith
    simp only [zero_mul, add_zero] at e
    rw [div_eq_div_iff (by positivity) (by positivity)] at e
    have : vl ^ 2 = vg ^ 2 := by
      have := mul_left_cancel₀ ha.ne' (show a * vg ^ 2 = a * vl ^ 2 by linarith)
      linarith
    nlinarith
  · have hRT : R * (7 / 10 * (8 * a / (27 * R * b))) = 1 * (7 / 10 * (8 * a / (27 * 1 * b))) := by
      field_simp
    have heq : cubicP R a b 0 0 (7 / 10 * (8 * a / (27 * R * b))) =
        cubicP 1 a b 0 0 (7 / 10 * (8 * a / (27 * 1 * b))) := by
      funext v; simp only [cubicP, hRT]
    rw [heq] at h
    exact Checked.Chemistry.Coexistence.vdW_coexistence_unique 1 a b vl vg ps one_pos ha hb hl h

/-- a > 0 is needed: with a = 0 the isotherm at temperature 0 is identically zero, every pair of
volumes is a coexistence state at pressure 0, and the claimed ratio fails. -/
theorem vdW_coexistence_unique_h2 : necessity% Checked.Chemistry.Coexistence.vdW_coexistence_unique 2 := by
  refine ⟨1, 0, 1, 2, 3, 0, one_pos, one_pos, by norm_num, ⟨by norm_num, ?_, ?_, ?_⟩, ?_⟩
  · simp [cubicP]
  · simp [cubicP]
  · simp [cubicP]
  · norm_num [RoundsTo, abs_le]


/-! ### Junk critical points of the cubic isotherm (run 2026-11-11T0028Z) -/

/-- A function that is differentiable just to the right of `v₀` and unbounded there satisfies the
critical-point condition at `v₀` in Lean's total calculus: it is not differentiable at `v₀`, and its
derivative is not differentiable at `v₀` either, so both junk derivatives are 0. -/
theorem crit_of_unbounded (p : ℝ → ℝ) (v₀ : ℝ)
    (hd : ∀ᶠ x in 𝓝[>] v₀, DifferentiableAt ℝ p x)
    (hu : Tendsto (fun x => |p x|) (𝓝[>] v₀) atTop) : Checked.Chemistry.CubicEOS.IsCriticalIsotherm p v₀ := by
  -- no bound on any right neighbourhood
  have nobound : ∀ M δ : ℝ, 0 < δ → ∃ x ∈ Ioo v₀ (v₀ + δ), M < |p x| := by
    intro M δ hδ
    have h1 : ∀ᶠ x in 𝓝[>] v₀, M < |p x| := hu.eventually_gt_atTop M
    have h2 : ∀ᶠ x in 𝓝[>] v₀, x ∈ Ioo v₀ (v₀ + δ) := Ioo_mem_nhdsGT (by linarith)
    obtain ⟨x, hx1, hx2⟩ := (h1.and h2).exists
    exact ⟨x, hx2, hx1⟩
  constructor
  · by_cases h : DifferentiableAt ℝ p v₀
    · exfalso
      have hc : Tendsto (fun x => |p x|) (𝓝[>] v₀) (𝓝 (|p v₀|)) :=
        ((h.continuousAt.tendsto).mono_left nhdsWithin_le_nhds).abs
      exact not_tendsto_nhds_of_tendsto_atTop hu _ hc
    · exact deriv_zero_of_not_differentiableAt h
  · by_cases h : DifferentiableAt ℝ (deriv p) v₀
    · exfalso
      have hc := h.continuousAt
      have hev : ∀ᶠ x in 𝓝[>] v₀, |deriv p x| ≤ |deriv p v₀| + 1 ∧ DifferentiableAt ℝ p x := by
        refine Filter.Eventually.and ?_ hd
        have : ∀ᶠ x in 𝓝 v₀, |deriv p x - deriv p v₀| < 1 := by
          have := Metric.tendsto_nhds.1 hc 1 one_pos
          simpa [Real.dist_eq] using this
        refine (this.filter_mono nhdsWithin_le_nhds).mono fun x hx => ?_
        have := abs_sub_abs_le_abs_sub (deriv p x) (deriv p v₀)
        linarith
      obtain ⟨u, hu', hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
      set M := |deriv p v₀| + 1
      set x₁ := (v₀ + u) / 2
      have hx₁ : x₁ ∈ Ioo v₀ u := ⟨by simp only [x₁]; linarith [hu'.out], by simp only [x₁]; linarith [hu'.out]⟩
      have hbound : ∀ x ∈ Ioo v₀ x₁, |p x| ≤ |p x₁| + M * (u - v₀) := by
        intro x hx
        have hs : Icc x x₁ ⊆ Ioo v₀ u := fun y hy => ⟨lt_of_lt_of_le hx.1 hy.1, lt_of_le_of_lt hy.2 hx₁.2⟩
        have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := p) (C := M) (s := Icc x x₁)
          (fun y hy => (hsub (hs hy)).2) (fun y hy => by rw [Real.norm_eq_abs]; exact (hsub (hs hy)).1)
          (convex_Icc x x₁) ⟨le_rfl, hx.2.le⟩ ⟨hx.2.le, le_rfl⟩
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (show (0:ℝ) ≤ x₁ - x by linarith [hx.2])] at h
        have hM : 0 ≤ M := by positivity
        have : M * (x₁ - x) ≤ M * (u - v₀) :=
          mul_le_mul_of_nonneg_left (by linarith [hx.1, hx₁.2]) hM
        have := abs_sub_abs_le_abs_sub (p x) (p x₁)
        rw [abs_sub_comm] at h
        linarith
      obtain ⟨x, hx, hxM⟩ := nobound (|p x₁| + M * (u - v₀)) (x₁ - v₀) (by linarith [hx₁.1])
      have : x ∈ Ioo v₀ x₁ := ⟨hx.1, by linarith [hx.2]⟩
      linarith [hbound x this]
    · exact deriv_zero_of_not_differentiableAt h


/-- `|h + k / g|` tends to infinity just to the right of a zero of `g` (with `h`, `g` continuous there
and `g` nonzero just to the right). -/
theorem abs_add_div_tendsto (h g : ℝ → ℝ) (k v₀ : ℝ) (hk : k ≠ 0) (hh : ContinuousAt h v₀)
    (hg : ContinuousAt g v₀) (hg0 : g v₀ = 0) (hne : ∀ᶠ x in 𝓝[>] v₀, g x ≠ 0) :
    Tendsto (fun x => |h x + k / g x|) (𝓝[>] v₀) atTop := by
  have hg' : Tendsto (fun x => |g x|) (𝓝[>] v₀) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, hne.mono fun x hx => abs_pos.2 hx⟩
    have := ((hg.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi v₀))).abs :
      Tendsto (fun x => |g x|) (𝓝[>] v₀) (𝓝 |g v₀|))
    simpa [hg0] using this
  have hinv : Tendsto (fun x => |k| * |g x|⁻¹) (𝓝[>] v₀) atTop :=
    (tendsto_inv_nhdsGT_zero.comp hg').const_mul_atTop (abs_pos.2 hk)
  have hb : ∀ᶠ x in 𝓝[>] v₀, |h x| ≤ |h v₀| + 1 := by
    have : ∀ᶠ x in 𝓝 v₀, |h x - h v₀| < 1 := by
      have := Metric.tendsto_nhds.1 hh.tendsto 1 one_pos
      simpa [Real.dist_eq] using this
    refine (this.filter_mono nhdsWithin_le_nhds).mono fun x hx => ?_
    have := abs_sub_abs_le_abs_sub (h x) (h v₀)
    linarith
  have h2 : Tendsto (fun x => |k| * |g x|⁻¹ - (|h v₀| + 1)) (𝓝[>] v₀) atTop :=
    tendsto_atTop_add_const_right _ _ hinv
  refine tendsto_atTop_mono' _ (hb.mono fun x hx => ?_) h2
  have e : |k / g x| = |k| * |g x|⁻¹ := by rw [abs_div, div_eq_mul_inv]
  have := abs_sub_abs_le_abs_sub (k / g x) (-h x)
  rw [sub_neg_eq_add, add_comm] at this
  rw [abs_neg] at this
  linarith

/-- The cubic isotherm as a sum of its two poles. -/
theorem cubicP_eq (R a b u w T x : ℝ) : Checked.Chemistry.CubicEOS.cubicP R a b u w T x =
    R * T / (x - b) + (-a) / (x ^ 2 + u * b * x + w * b ^ 2) := by
  unfold Checked.Chemistry.CubicEOS.cubicP; rw [neg_div]; ring

theorem cubicP_diff (R a b u w T x : ℝ) (hx : x - b ≠ 0) (hD : x ^ 2 + u * b * x + w * b ^ 2 ≠ 0) :
    DifferentiableAt ℝ (Checked.Chemistry.CubicEOS.cubicP R a b u w T) x := by
  unfold Checked.Chemistry.CubicEOS.cubicP
  apply DifferentiableAt.sub
  · exact (differentiableAt_const _).div (differentiableAt_id.sub_const _) hx
  · exact (differentiableAt_const _).div (by fun_prop) hD

/-- At the co-volume `v = b` (where `R T / (v − b)` has its pole) the cubic isotherm meets the
critical-point condition by the junk derivatives, whenever `R T ≠ 0` and the attraction denominator is
nonzero at `b`. -/
theorem crit_at_b (R a b u w T : ℝ) (hRT : R * T ≠ 0) (hD : b ^ 2 + u * b * b + w * b ^ 2 ≠ 0) :
    Checked.Chemistry.CubicEOS.IsCriticalIsotherm (Checked.Chemistry.CubicEOS.cubicP R a b u w T) b := by
  have hDc : ContinuousAt (fun x => x ^ 2 + u * b * x + w * b ^ 2) b := by fun_prop
  have hDne : ∀ᶠ x in 𝓝 b, x ^ 2 + u * b * x + w * b ^ 2 ≠ 0 := hDc.eventually_ne hD
  apply crit_of_unbounded
  · filter_upwards [hDne.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hxb
    exact cubicP_diff R a b u w T x (sub_ne_zero.2 (ne_of_gt hxb)) hx
  · have := abs_add_div_tendsto (fun x => (-a) / (x ^ 2 + u * b * x + w * b ^ 2)) (fun x => x - b)
      (R * T) b hRT (continuousAt_const.div hDc hD) (by fun_prop) (by simp)
      (Filter.mem_of_superset (self_mem_nhdsWithin (s := Ioi b)) fun x (hx : b < x) =>
        sub_ne_zero.2 (ne_of_gt hx))
    refine this.congr fun x => ?_
    rw [cubicP_eq]; ring_nf

/-- At a zero `v₀ > b` of the attraction denominator the cubic isotherm (with `a ≠ 0`) meets the
critical-point condition by the junk derivatives. -/
theorem crit_at_root (R a b u w T v₀ : ℝ) (hb : b < v₀) (ha : a ≠ 0)
    (hD : v₀ ^ 2 + u * b * v₀ + w * b ^ 2 = 0)
    (hne : ∀ᶠ x in 𝓝[>] v₀, x ^ 2 + u * b * x + w * b ^ 2 ≠ 0) :
    Checked.Chemistry.CubicEOS.IsCriticalIsotherm (Checked.Chemistry.CubicEOS.cubicP R a b u w T) v₀ := by
  apply crit_of_unbounded
  · filter_upwards [hne, self_mem_nhdsWithin] with x hx hxv
    exact cubicP_diff R a b u w T x (sub_ne_zero.2 (ne_of_gt (hb.trans hxv))) hx
  · have := abs_add_div_tendsto (fun x => R * T / (x - b)) (fun x => x ^ 2 + u * b * x + w * b ^ 2)
      (-a) v₀ (neg_ne_zero.2 ha)
      (continuousAt_const.div (continuousAt_id.sub continuousAt_const) (sub_ne_zero.2 (ne_of_gt hb)))
      (by fun_prop) hD hne
    exact this.congr fun x => by rw [cubicP_eq]


/-- `0 < b` is needed for the van der Waals constants: with b = −1, T = 0 the isotherm −1/v² has its
pole at v = 0 > b, where Lean's junk derivatives meet the critical-point condition, and the
compressibility P v/(R T) is 0 (division by R T = 0), not 3/8. -/
theorem vdW_constants_h2 : necessity% Checked.Chemistry.CubicEOS.vdW_constants 2 := by
  refine ⟨1, 1, -1, 0, 0, one_pos, by norm_num,
    crit_at_root 1 1 (-1) 0 0 0 0 (by norm_num) one_ne_zero (by norm_num) ?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    intro h; nlinarith [sq_pos_of_pos hx]
  · rintro ⟨h, -⟩; norm_num at h

/-- `b < v` is needed for the van der Waals constants: at v = b (the pole of R T/(v − b)) the junk
derivatives meet the critical-point condition and P v/(R T) = −1, not 3/8. -/
theorem vdW_constants_h3 : necessity% Checked.Chemistry.CubicEOS.vdW_constants 3 := by
  refine ⟨1, 1, 1, 1, 1, one_pos, one_pos, crit_at_b 1 1 1 0 0 1 (by norm_num) (by norm_num), ?_⟩
  rintro ⟨h, -⟩; norm_num [Checked.Chemistry.CubicEOS.cubicP] at h

/-- `0 < b` is needed for the Redlich–Kwong constants (pole of −1/(v(v − 1)) at v = 0 > b = −1, T = 0). -/
theorem rk_constants_h2 : necessity% Checked.Chemistry.CubicEOS.rk_constants 2 := by
  refine ⟨1, 1, -1, 0, 0, one_pos, by norm_num,
    crit_at_root 1 1 (-1) 1 0 0 0 (by norm_num) one_ne_zero (by norm_num) ?_, ?_⟩
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    intro h; nlinarith [hx.1, hx.2]
  · rintro ⟨h, -⟩; norm_num at h

/-- `b < v` is needed for the Redlich–Kwong constants (v = b = 1: P v/(R T) = −1/2, not 1/3). -/
theorem rk_constants_h3 : necessity% Checked.Chemistry.CubicEOS.rk_constants 3 := by
  refine ⟨1, 1, 1, 1, 1, one_pos, one_pos, crit_at_b 1 1 1 1 0 1 (by norm_num) (by norm_num), ?_⟩
  rintro ⟨h, -⟩; norm_num [Checked.Chemistry.CubicEOS.cubicP] at h

/-- `0 < b` is needed for the Peng–Robinson constants (b = −1, T = 0: pole of −1/(v² − 2v − 1) at
v = 1 + √2 > b; the compressibility is 0, which does not round to 0.3074). -/
theorem pr_constants_h2 : necessity% Checked.Chemistry.CubicEOS.pr_constants 2 := by
  have s2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have s0 := Real.sqrt_nonneg 2
  refine ⟨1, 1, -1, 0, 1 + Real.sqrt 2, one_pos, by linarith,
    crit_at_root 1 1 (-1) 2 (-1) 0 (1 + Real.sqrt 2) (by linarith) one_ne_zero (by nlinarith) ?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with x (hx : 1 + Real.sqrt 2 < x)
    intro h; nlinarith
  · rintro ⟨h, -⟩; norm_num [RoundsTo, abs_le] at h

/-- `b < v` is needed for the Peng–Robinson constants (v = b = 1: P v/(R T) = −1/2, which does not
round to 0.3074). -/
theorem pr_constants_h3 : necessity% Checked.Chemistry.CubicEOS.pr_constants 3 := by
  refine ⟨1, 1, 1, 1, 1, one_pos, one_pos, crit_at_b 1 1 1 2 (-1) 1 (by norm_num) (by norm_num), ?_⟩
  rintro ⟨h, -⟩; norm_num [Checked.Chemistry.CubicEOS.cubicP, RoundsTo, abs_le] at h

/-- `b < v` is needed in the characterisation of critical points: at v = b the junk derivatives meet
the critical-point condition, but the critical cubic is −2 b³ ≠ 0. -/
theorem isCritical_iff_h2 : necessity% Checked.Chemistry.CubicEOS.isCritical_iff 2 := by
  refine ⟨1, 1, 1, 0, 0, 1, 1, one_pos, by norm_num, ?_⟩
  intro h
  have := (h.1 (crit_at_b 1 1 1 0 0 1 (by norm_num) (by norm_num))).1
  norm_num at this

/-- A positive attraction denominator is needed in the characterisation of critical points: with
u = 0, w = −4, b = 1 the denominator v² − 4 vanishes at v = 2 > b, the junk derivatives meet the
critical-point condition there, and the critical cubic is 16 ≠ 0. -/
theorem isCritical_iff_h3 : necessity% Checked.Chemistry.CubicEOS.isCritical_iff 3 := by
  refine ⟨1, 1, 1, 0, -4, 1, 2, one_pos, by norm_num, ?_⟩
  intro h
  have hc := crit_at_root 1 1 1 0 (-4) 1 2 (by norm_num) one_ne_zero (by norm_num) (by
    filter_upwards [self_mem_nhdsWithin] with x (hx : 2 < x)
    intro h; nlinarith)
  have := (h.1 hc).1
  norm_num at this

end Chemistry

section Cosmography
open Checked.Records Checked.Cosmography Checked.Cosmography.Aviles Checked.Trust.NV

/-! ### Cosmography: model laws and the printed-coefficient condition (run 2026-11-11T0028Z)

De Sitter `a = exp` (every cosmographic coefficient 1, deceleration −1) meets every smoothness
hypothesis and falsifies the coefficient formulas of a model law with a matter density it does not
have; at Ω = 1 the CPL dark-energy terms vanish, so the printed fifth coefficient is the true one. -/

/-- The flat ΛCDM law is needed for its coefficients: de Sitter has deceleration −1, not 3Ω/2 − 1 = 1/2 at Ω = 1. -/
theorem flatLCDM_coeffs_h1 : necessity% Checked.Cosmography.Aviles.flatLCDM_coeffs 1 := by
  refine ⟨1, Real.exp, 0, dS_smooth _, ?_⟩
  rintro ⟨h, -⟩; rw [dS_decel] at h; norm_num at h

/-- The flat CPL law is needed for its coefficients: de Sitter has deceleration −1, not 1/2 at Ω = 1. -/
theorem flatCPL_coeffs_h1 : necessity% Checked.Cosmography.CPL.flatCPL_coeffs 1 := by
  refine ⟨1, 0, 0, Real.exp, 0, dS_smooth _, ?_⟩
  rintro ⟨h, -⟩; rw [dS_decel] at h; norm_num at h

/-- The flat CPL law is needed for the misprint statement: de Sitter's fifth coefficient 1 equals the
printed formula at Ω = 0, w₀ = −1, wₐ = −96/7, where (1 − Ω)(7 − Ω)wₐ = −96 ≠ 0. -/
theorem printedL0_ne_h1 : necessity% Checked.Cosmography.CPL.printedL0_ne 1 := by
  refine ⟨0, -1, -96 / 7, Real.exp, 0, dS_smooth _, by norm_num, ?_⟩
  intro h; apply h; rw [dS_coeff]; norm_num

/-- The condition (1 − Ω)(7 − Ω)wₐ ≠ 0 is needed for the misprint statement: at Ω = 1 every flat CPL
model's fifth coefficient equals the printed formula. -/
theorem printedL0_ne_h3 : necessity% Checked.Cosmography.CPL.printedL0_ne 3 := by
  obtain ⟨a, hL, hs⟩ := Checked.Cosmography.CPLExistence.exists_flatCPL 1 0 0
  refine ⟨1, 0, 0, a, 0, hL, hs, ?_⟩
  intro h; apply h
  rw [(Checked.Cosmography.CPL.flatCPL_coeffs 1 0 0 a 0 hL hs).2.2.2]; norm_num

/-- The same condition is needed for the existence of a model refuting the printed formula: at
Ω = 1 no flat CPL model does. -/
theorem cpl_printedL0_false_at_h1 : necessity% Checked.Cosmography.CPLExistence.printedL0_false_at 1 := by
  refine ⟨1, 0, 0, ?_⟩
  rintro ⟨a, hL, hs, h⟩; apply h
  rw [(Checked.Cosmography.CPL.flatCPL_coeffs 1 0 0 a 0 hL hs).2.2.2]; norm_num

/-- The ΛCDM law is needed for record F1: de Sitter's fifth coefficient is 1, which does not round to 3.115. -/
theorem F1_l0_h1 : necessity% Checked.Records.F1_l0 1 := by
  refine ⟨Real.exp, 0, dS_smooth _, ?_⟩
  rw [dS_coeff]; norm_num [RoundsTo, abs_le]

/-- The CPL law is needed for record F2 (toy): de Sitter's fifth coefficient 1 does not round to 0.809. -/
theorem F2_toy_h1 : necessity% Checked.Records.F2_toy 1 := by
  refine ⟨Real.exp, 0, dS_smooth _, ?_⟩
  rintro ⟨h, -⟩; rw [dS_coeff] at h; norm_num [RoundsTo, abs_le] at h

/-- The CPL law is needed for record F2 (error): with de Sitter and w₀ = 0 the difference is
1 − printed ≈ 1.84, which does not round to 2.345. -/
theorem F2_error_h1 : necessity% Checked.Records.F2_error 1 := by
  refine ⟨0, Real.exp, 0, dS_smooth _, ?_⟩
  rw [dS_coeff]; norm_num [RoundsTo, abs_le, printedCLSL0]

/-- The ΛCDM law is needed for record F3: de Sitter's corrected D⁴ is 1/5, which does not round to 0.2153. -/
theorem F3_D4_LCDM_h1 : necessity% Checked.Records.F3_D4_LCDM 1 := by
  refine ⟨Real.exp, 0, dS_smooth _, ?_⟩
  rintro ⟨h, -⟩
  rw [dS_decel, dS_coeff, dS_coeff, dS_coeff] at h
  norm_num [RoundsTo, abs_le, Checked.Cosmography.CCS.correctD4] at h

end Cosmography

section Lookback
open Checked.Cosmography Asymptotics

/-! ### The lookback-time expansions (run 2026-11-11T0028Z) -/

/-- With a vanishing present scale factor the redshift is −1 for every emission time (junk division). -/
theorem redshift_of_a0 (a : ℝ → ℝ) (t₀ : ℝ) (h0 : a t₀ = 0) (t : ℝ) : redshift a t₀ t = -1 := by
  simp [redshift, h0]

/-- `a t₀ ≠ 0` is redundant in the second-order lookback expansion (Lean's total division): if
a(t₀) = 0 the redshift is −1 and the Hubble rate 0, so the remainder is t₀ − t, which is o(1). -/
theorem lookback_second_order_r3 : dropped% Checked.Cosmography.lookback_second_order 3 := by
  intro a t₀ ha ha' hH
  by_cases h0 : a t₀ = 0
  · have e2 : hubble a t₀ = 0 := by simp [hubble, h0]
    simp only [redshift_of_a0 a t₀ h0, e2, div_zero, sub_zero]
    norm_num
    have : Tendsto (fun t : ℝ => t₀ - t) (𝓝 t₀) (𝓝 (t₀ - t₀)) := tendsto_const_nhds.sub tendsto_id
    simpa using this
  · exact Checked.Cosmography.lookback_second_order a t₀ ha ha' h0 hH

/-- The same for the big-O form with a cubic remainder: the remainder t₀ − t is bounded. -/
theorem lookback_second_order_bigO_r2 : dropped% Checked.Cosmography.lookback_second_order_bigO 2 := by
  intro a t₀ ha hH
  by_cases h0 : a t₀ = 0
  · have e2 : hubble a t₀ = 0 := by simp [hubble, h0]
    simp only [redshift_of_a0 a t₀ h0, e2, div_zero, sub_zero]
    norm_num
    have : Tendsto (fun t : ℝ => t₀ - t) (𝓝 t₀) (𝓝 (t₀ - t₀)) := tendsto_const_nhds.sub tendsto_id
    exact this.abs.isBoundedUnder_le
  · exact Checked.Cosmography.lookback_second_order_bigO a t₀ ha h0 hH

/-- The scale factor 1 + t² (zero velocity at t = 0). -/
noncomputable def flatStart (t : ℝ) : ℝ := 1 + t ^ 2

theorem flatStart_deriv : deriv flatStart = fun t => 2 * t := by
  funext t
  have h : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * t) t := by
    simpa using (hasDerivAt_pow 2 t).const_add 1
  exact h.deriv

/-- No bound |t| ≤ C t² holds near 0. -/
theorem not_abs_le_sq (C : ℝ) : ¬ ∀ᶠ t in 𝓝 (0 : ℝ), |t| ≤ C * t ^ 2 := by
  intro hC
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hC
  set c := |C| + 1
  have hc : 0 < c := by positivity
  set t := min (δ / 2) (1 / (2 * c))
  have ht : 0 < t := lt_min (by linarith) (by positivity)
  have ht1 : t ≤ 1 / (2 * c) := min_le_right _ _
  have htδ : t ≤ δ / 2 := min_le_left _ _
  have hd : dist t 0 < δ := by rw [Real.dist_eq, sub_zero, abs_of_pos ht]; linarith
  have key := hball hd
  rw [abs_of_pos ht] at key
  have hct : c * t ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left ht1 hc.le
    rwa [show c * (1 / (2 * c)) = 1 / 2 by field_simp] at this
  have hC : C * t ^ 2 ≤ c * t ^ 2 := by
    have := le_abs_self C; nlinarith [sq_nonneg t]
  nlinarith

/-- The redshift of 1 + t² at observation time 0: z = −t²/(1 + t²), so |z| ≤ t². -/
theorem flatStart_z (t : ℝ) : |redshift flatStart 0 t| ≤ t ^ 2 := by
  have hz : redshift flatStart 0 t = -(t ^ 2 / (1 + t ^ 2)) := by
    simp [redshift, flatStart]; field_simp; ring
  rw [hz, abs_neg, abs_of_nonneg (by positivity)]
  exact div_le_self (by positivity) (by nlinarith [sq_nonneg t])

/-- For 1 + t², the function −t is not O(z³) at 0, where z is the redshift. -/
theorem flatStart_not_bigO :
    ¬ (fun t : ℝ => (0 : ℝ) - t) =O[𝓝 0] (fun t => redshift flatStart 0 t ^ 3) := by
  intro h
  obtain ⟨C, hC⟩ := h.bound
  apply not_abs_le_sq (|C|)
  filter_upwards [hC, Metric.ball_mem_nhds (0 : ℝ) one_pos] with t ht ht1
  simp only [zero_sub, norm_neg, Real.norm_eq_abs, abs_pow] at ht
  have hz := flatStart_z t
  have ht1' : |t| < 1 := by simpa [Real.dist_eq] using ht1
  have hsq : t ^ 2 ≤ 1 := by nlinarith [abs_nonneg t, sq_abs t]
  have h3 : |redshift flatStart 0 t| ^ 3 ≤ t ^ 2 := by
    have h0 := abs_nonneg (redshift flatStart 0 t)
    calc |redshift flatStart 0 t| ^ 3 ≤ (t ^ 2) ^ 3 := pow_le_pow_left₀ h0 hz 3
      _ ≤ t ^ 2 := by nlinarith [pow_le_one₀ (sq_nonneg t) hsq (n := 2), sq_nonneg t]
  calc |t| ≤ C * |redshift flatStart 0 t| ^ 3 := ht
    _ ≤ |C| * |redshift flatStart 0 t| ^ 3 := by
        gcongr; exact le_abs_self C
    _ ≤ |C| * t ^ 2 := by gcongr

/-- For 1 + t², the function −t is not o(z²) at 0. -/
theorem flatStart_not_littleO :
    ¬ (fun t : ℝ => (0 : ℝ) - t) =o[𝓝 0] (fun t => redshift flatStart 0 t ^ 2) := by
  intro h
  apply not_abs_le_sq 1
  filter_upwards [h.bound one_pos, Metric.ball_mem_nhds (0 : ℝ) one_pos] with t ht ht1
  simp only [zero_sub, norm_neg, Real.norm_eq_abs, abs_pow] at ht
  have hz := flatStart_z t
  have ht1' : |t| < 1 := by simpa [Real.dist_eq] using ht1
  have hsq : t ^ 2 ≤ 1 := by nlinarith [abs_nonneg t, sq_abs t]
  have h2 : |redshift flatStart 0 t| ^ 2 ≤ t ^ 2 := by
    have h0 := abs_nonneg (redshift flatStart 0 t)
    calc |redshift flatStart 0 t| ^ 2 ≤ (t ^ 2) ^ 2 := pow_le_pow_left₀ h0 hz 2
      _ ≤ t ^ 2 := by nlinarith [sq_nonneg t]
  linarith

/-- `deriv a t₀ ≠ 0` is needed in the big-O lookback expansion: a = 1 + t² at t₀ = 0. -/
theorem lookback_second_order_bigO_h3 : necessity% Checked.Cosmography.lookback_second_order_bigO 3 := by
  refine ⟨flatStart, 0, (show ContDiff ℝ 3 flatStart from ContDiff.add contDiff_const (contDiff_id.pow 2)).contDiffAt, by simp [flatStart], ?_⟩
  have hd : deriv flatStart 0 = 0 := by rw [flatStart_deriv]; ring
  have hH : hubble flatStart 0 = 0 := by simp [hubble, hd]
  rw [hH]; simp only [div_zero, sub_zero]
  exact flatStart_not_bigO

/-- `deriv a t₀ ≠ 0` is needed in the little-o lookback expansion: a = 1 + t² at t₀ = 0. -/
theorem lookback_second_order_h4 : necessity% Checked.Cosmography.lookback_second_order 4 := by
  have hdiff : Differentiable ℝ flatStart := by unfold flatStart; fun_prop
  refine ⟨flatStart, 0, Eventually.of_forall fun t => hdiff t, ?_, by simp [flatStart], ?_⟩
  · rw [flatStart_deriv]; fun_prop
  · have hd : deriv flatStart 0 = 0 := by rw [flatStart_deriv]; ring
    have hH : hubble flatStart 0 = 0 := by simp [hubble, hd]
    rw [hH]; simp only [div_zero, sub_zero]
    exact flatStart_not_littleO

end Lookback

section HubbleScale
/-! ### A nonzero scale factor is implied by a nonzero Hubble rate (run 2026-11-11T0028Z)

`hubble a t₀ = deriv a t₀ / a t₀`, and division by zero gives zero, so a nonzero Hubble rate forces a
nonzero present scale factor: the hypothesis `a t₀ ≠ 0` is redundant in every headline that also
assumes `hubble a t₀ ≠ 0`. -/

theorem ne_a0_of_hubble {a : ℝ → ℝ} {t₀ : ℝ} (h : Checked.Cosmography.hubble a t₀ ≠ 0) : a t₀ ≠ 0 :=
  fun h0 => h (by simp [Checked.Cosmography.hubble, h0])

theorem lookback_fifth_order_r2 : dropped% Checked.Cosmography.CCS.lookback_fifth_order 2 := by
  intros
  apply Checked.Cosmography.CCS.lookback_fifth_order <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem printedD4_fails_r2 : dropped% Checked.Cosmography.CCS.printedD4_fails 2 := by
  intros
  apply Checked.Cosmography.CCS.printedD4_fails <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem printedD4_fails_past_r2 : dropped% Checked.Cosmography.CCS.printedD4_fails_past 2 := by
  intros
  apply Checked.Cosmography.CCS.printedD4_fails_past <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem lumDist_y_third_order_r2 : dropped% Checked.Cosmography.BambaY.lumDist_y_third_order 2 := by
  intros
  apply Checked.Cosmography.BambaY.lumDist_y_third_order <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem printedD2y_fails_r2 : dropped% Checked.Cosmography.BambaY.printedD2y_fails 2 := by
  intros
  apply Checked.Cosmography.BambaY.printedD2y_fails <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem printedD2y_fails_past_r2 : dropped% Checked.Cosmography.BambaY.printedD2y_fails_past 2 := by
  intros
  apply Checked.Cosmography.BambaY.printedD2y_fails_past <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem dQ_y_third_order_r2 : dropped% Checked.Cosmography.CVdQ.dQ_y_third_order 2 := by
  intros
  apply Checked.Cosmography.CVdQ.dQ_y_third_order <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem printedQ2_fails_past_r2 : dropped% Checked.Cosmography.CVdQ.printedQ2_fails_past 2 := by
  intros
  apply Checked.Cosmography.CVdQ.printedQ2_fails_past <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem lumDist_y_fifth_order_r2 : dropped% Checked.Cosmography.BambaK.lumDist_y_fifth_order 2 := by
  intros
  apply Checked.Cosmography.BambaK.lumDist_y_fifth_order <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem printedD3y_fails_r2 : dropped% Checked.Cosmography.BambaK.printedD3y_fails 2 := by
  intros
  apply Checked.Cosmography.BambaK.printedD3y_fails <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem printedD3y_fails_past_r2 : dropped% Checked.Cosmography.BambaK.printedD3y_fails_past 2 := by
  intros
  apply Checked.Cosmography.BambaK.printedD3y_fails_past <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem printedD4y_fails_r2 : dropped% Checked.Cosmography.BambaK.printedD4y_fails 2 := by
  intros
  apply Checked.Cosmography.BambaK.printedD4y_fails <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem printedD4y_fails_past_r2 : dropped% Checked.Cosmography.BambaK.printedD4y_fails_past 2 := by
  intros
  apply Checked.Cosmography.BambaK.printedD4y_fails_past <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem angDist_y_fifth_order_r2 : dropped% Checked.Cosmography.BambaA.angDist_y_fifth_order 2 := by
  intros
  apply Checked.Cosmography.BambaA.angDist_y_fifth_order <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem printedDA3_fails_r2 : dropped% Checked.Cosmography.BambaA.printedDA3_fails 2 := by
  intros
  apply Checked.Cosmography.BambaA.printedDA3_fails <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem printedDA3_fails_past_r2 : dropped% Checked.Cosmography.BambaA.printedDA3_fails_past 2 := by
  intros
  apply Checked.Cosmography.BambaA.printedDA3_fails_past <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem printedDA4_fails_r2 : dropped% Checked.Cosmography.BambaA.printedDA4_fails 2 := by
  intros
  apply Checked.Cosmography.BambaA.printedDA4_fails <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem printedDA4_fails_past_r2 : dropped% Checked.Cosmography.BambaA.printedDA4_fails_past 2 := by
  intros
  apply Checked.Cosmography.BambaA.printedDA4_fails_past <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem lumDist_z_fifth_order_r2 : dropped% Checked.Cosmography.BambaZ.lumDist_z_fifth_order 2 := by
  intros
  apply Checked.Cosmography.BambaZ.lumDist_z_fifth_order <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem angDist_z_fifth_order_r2 : dropped% Checked.Cosmography.BambaZ.angDist_z_fifth_order 2 := by
  intros
  apply Checked.Cosmography.BambaZ.angDist_z_fifth_order <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem printedDL4z_fails_past_r2 : dropped% Checked.Cosmography.BambaZ.printedDL4z_fails_past 2 := by
  intros
  apply Checked.Cosmography.BambaZ.printedDL4z_fails_past <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem printedDA4z_fails_past_r2 : dropped% Checked.Cosmography.BambaZ.printedDA4z_fails_past 2 := by
  intros
  apply Checked.Cosmography.BambaZ.printedDA4z_fails_past <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem demDL4_fails_past_r2 : dropped% Checked.Cosmography.DemianskiZ.demDL4_fails_past 2 := by
  intros
  apply Checked.Cosmography.DemianskiZ.demDL4_fails_past <;> first | assumption | exact ne_a0_of_hubble (by assumption)

theorem demDA4_fails_past_r2 : dropped% Checked.Cosmography.DemianskiZ.demDA4_fails_past 2 := by
  intros
  apply Checked.Cosmography.DemianskiZ.demDA4_fails_past <;> first | assumption | exact ne_a0_of_hubble (by assumption)

end HubbleScale

section StaticModel
open Checked.Cosmography Checked.Cosmography.Aviles Checked.Cosmography.BambaY Asymptotics

/-- A nonzero Hubble rate is needed for the misprint statement on the second luminosity-distance
coefficient in y: the static model a ≡ 1 meets every other hypothesis (11 − 5q + 3q² − j = 11 with the
junk values q = j = 0), its redshift is 0 and its remainder vanishes, so the printed series is not refuted. -/
theorem printedD2y_fails_h3 : necessity% Checked.Cosmography.BambaY.printedD2y_fails 3 := by
  have hH : hubble (fun _ : ℝ => (1 : ℝ)) 0 = 0 := by simp [hubble]
  refine ⟨fun _ => 1, 0, contDiffAt_const, one_ne_zero, ?_, ?_⟩
  · simp [decel, cosmoCoeff, hH]
  · have hz : ∀ t, remainderY printedD2y (fun _ : ℝ => (1 : ℝ)) 0 t = 0 := by
      intro t; simp [remainderY, seriesY, yred, redshift, hH]
    simp only [hz]
    exact isLittleO_zero _ _

end StaticModel

section SeriesHubble
open Checked.Cosmography Checked.Cosmography.Aviles Asymptotics

/-! ### A nonzero Hubble rate is needed in the cosmographic series (run 2026-11-11T0028Z)

With the scale factor 1 + t² at t₀ = 0 the velocity, hence the Hubble rate, is 0, every junk
coefficient (deceleration, jerk, …) is 0, and each remainder `H₀ · distance − x (1 + c₁ x + …)`
reduces to −x(1 + c₁x + …), which is of exact order x, not o(xⁿ) for n ≥ 2 (`x` is the redshift
z = −t²/(1 + t²) or y = z/(1 + z) = −t²). -/

/-- Core: −x·g(x) with g → 1 is not o(xⁿ), n ≥ 2, where x → 0 and x ≠ 0 frequently. -/
theorem not_littleO_core (x g : ℝ → ℝ) (t₀ H : ℝ) (D : ℝ → ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hH : H = 0) (hx : Tendsto x (𝓝 t₀) (𝓝 0)) (hg : ContinuousAt g 0) (hg0 : g 0 = 1)
    (hfreq : ∃ᶠ t in 𝓝 t₀, x t ≠ 0) :
    ¬ (fun t => H * D t - x t * g (x t)) =o[𝓝 t₀] (fun t => x t ^ n) := by
  intro h
  subst hH
  have h1 := h.bound (show (0 : ℝ) < 1 / 4 by norm_num)
  have h2 : ∀ᶠ t in 𝓝 t₀, |g (x t) - 1| < 1 / 2 := by
    have := Metric.tendsto_nhds.1 ((hg.tendsto.comp hx)) (1 / 2) (by norm_num)
    simpa [Real.dist_eq, hg0] using this
  have h3 : ∀ᶠ t in 𝓝 t₀, |x t| < 1 := by
    have := Metric.tendsto_nhds.1 hx 1 one_pos
    simpa [Real.dist_eq] using this
  apply hfreq
  filter_upwards [h1, h2, h3] with t ht1 ht2 ht3
  simp only [zero_mul, zero_sub, norm_neg, norm_mul, Real.norm_eq_abs, abs_pow] at ht1
  have hxn : |x t| ^ n ≤ |x t| := by
    calc |x t| ^ n ≤ |x t| ^ 1 := pow_le_pow_of_le_one (abs_nonneg _) ht3.le (by omega)
      _ = |x t| := pow_one _
  have hg' : 1 / 2 ≤ |g (x t)| := by
    have := abs_sub_abs_le_abs_sub 1 (g (x t)); rw [abs_sub_comm] at this; norm_num at this; linarith
  have : |x t| * (1 / 2) ≤ |x t| * (1 / 4) := by
    calc |x t| * (1 / 2) ≤ |x t| * |g (x t)| := mul_le_mul_of_nonneg_left hg' (abs_nonneg _)
      _ ≤ 1 / 4 * |x t| ^ n := ht1
      _ ≤ 1 / 4 * |x t| := by gcongr
      _ = |x t| * (1 / 4) := by ring
  have : |x t| ≤ 0 := by nlinarith [abs_nonneg (x t)]
  exact not_not.2 (abs_nonpos_iff.1 this)

theorem not_littleO_deg4 (x : ℝ → ℝ) (t₀ H c₁ c₂ c₃ c₄ : ℝ) (D : ℝ → ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hH : H = 0) (hx : Tendsto x (𝓝 t₀) (𝓝 0)) (hfreq : ∃ᶠ t in 𝓝 t₀, x t ≠ 0) :
    ¬ (fun t => H * D t - x t * (1 + c₁ * x t + c₂ * x t ^ 2 + c₃ * x t ^ 3 + c₄ * x t ^ 4))
      =o[𝓝 t₀] (fun t => x t ^ n) :=
  not_littleO_core x (fun z => 1 + c₁ * z + c₂ * z ^ 2 + c₃ * z ^ 3 + c₄ * z ^ 4) t₀ H D n hn hH hx
    (by fun_prop) (by simp) hfreq

theorem not_littleO_deg2 (x : ℝ → ℝ) (t₀ H c₁ c₂ : ℝ) (D : ℝ → ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hH : H = 0) (hx : Tendsto x (𝓝 t₀) (𝓝 0)) (hfreq : ∃ᶠ t in 𝓝 t₀, x t ≠ 0) :
    ¬ (fun t => H * D t - x t * (1 + c₁ * x t + c₂ * x t ^ 2)) =o[𝓝 t₀] (fun t => x t ^ n) :=
  not_littleO_core x (fun z => 1 + c₁ * z + c₂ * z ^ 2) t₀ H D n hn hH hx (by fun_prop) (by simp) hfreq

theorem not_littleO_deg2m (x : ℝ → ℝ) (t₀ H c₁ c₂ : ℝ) (D : ℝ → ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hH : H = 0) (hx : Tendsto x (𝓝 t₀) (𝓝 0)) (hfreq : ∃ᶠ t in 𝓝 t₀, x t ≠ 0) :
    ¬ (fun t => H * D t - x t * (1 - c₁ * x t + c₂ * x t ^ 2)) =o[𝓝 t₀] (fun t => x t ^ n) :=
  not_littleO_core x (fun z => 1 - c₁ * z + c₂ * z ^ 2) t₀ H D n hn hH hx (by fun_prop) (by simp) hfreq

theorem flatStart_hubble : hubble flatStart 0 = 0 := by
  simp [hubble, flatStart_deriv]

theorem flatStart_redshift (t : ℝ) : redshift flatStart 0 t = -(t ^ 2 / (1 + t ^ 2)) := by
  simp [redshift, flatStart]; field_simp; ring

theorem flatStart_yred (t : ℝ) : Checked.Cosmography.BambaY.yred flatStart 0 t = -t ^ 2 := by
  simp only [Checked.Cosmography.BambaY.yred, flatStart_redshift]
  have h1 : (0 : ℝ) < 1 + t ^ 2 := by positivity
  field_simp
  ring

theorem flatStart_z_tendsto : Tendsto (fun t => redshift flatStart 0 t) (𝓝 0) (𝓝 0) := by
  simp only [flatStart_redshift]
  have : Continuous fun t : ℝ => -(t ^ 2 / (1 + t ^ 2)) :=
    by exact (continuous_pow 2 |>.div (continuous_const.add (continuous_pow 2)) (fun t => (by positivity : (0:ℝ) < 1 + t ^ 2).ne')).neg
  simpa using this.tendsto 0

theorem flatStart_y_tendsto : Tendsto (fun t => Checked.Cosmography.BambaY.yred flatStart 0 t) (𝓝 0) (𝓝 0) := by
  simp only [flatStart_yred]
  have : Continuous fun t : ℝ => -t ^ 2 := by fun_prop
  simpa using this.tendsto 0

theorem frequently_ne_of_ne (x : ℝ → ℝ) (hx : ∀ t, t ≠ 0 → x t ≠ 0) : ∃ᶠ t in 𝓝 (0 : ℝ), x t ≠ 0 := by
  intro h
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.1 h
  have : dist (δ / 2) 0 < δ := by rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith
  exact hb this (hx _ (by positivity))

theorem flatStart_z_freq : ∃ᶠ t in 𝓝 (0 : ℝ), redshift flatStart 0 t ≠ 0 :=
  frequently_ne_of_ne _ fun t ht => by
    rw [flatStart_redshift]; have : 0 < t ^ 2 := by positivity
    exact neg_ne_zero.2 (div_pos this (by positivity)).ne'

theorem flatStart_y_freq : ∃ᶠ t in 𝓝 (0 : ℝ), Checked.Cosmography.BambaY.yred flatStart 0 t ≠ 0 :=
  frequently_ne_of_ne _ fun t ht => by rw [flatStart_yred]; exact neg_ne_zero.2 (pow_ne_zero 2 ht)

theorem flatStart_smooth (n : WithTop ℕ∞) : ContDiffAt ℝ n flatStart 0 :=
  (show ContDiff ℝ n flatStart from ContDiff.add contDiff_const (contDiff_id.pow 2)).contDiffAt

theorem flatStart_ne : flatStart 0 ≠ 0 := by simp [flatStart]

/-- A nonzero Hubble rate is needed in the fifth-order lookback series (scale factor 1 + t²). -/
theorem lookback_fifth_order_h3 : necessity% Checked.Cosmography.CCS.lookback_fifth_order 3 := by
  refine ⟨flatStart, 0, flatStart_smooth _, flatStart_ne, ?_⟩
  unfold Checked.Cosmography.CCS.remainder Checked.Cosmography.CCS.series
  exact not_littleO_deg4 _ _ _ _ _ _ _ _ 5 (by norm_num) flatStart_hubble flatStart_z_tendsto flatStart_z_freq

/-- A nonzero Hubble rate is needed in the third-order luminosity-distance series in y. -/
theorem lumDist_y_third_order_h3 : necessity% Checked.Cosmography.BambaY.lumDist_y_third_order 3 := by
  refine ⟨flatStart, 0, flatStart_smooth _, flatStart_ne, ?_⟩
  unfold Checked.Cosmography.BambaY.remainderY Checked.Cosmography.BambaY.seriesY
  exact not_littleO_deg2 _ _ _ _ _ _ 3 (by norm_num) flatStart_hubble flatStart_y_tendsto flatStart_y_freq

/-- A nonzero Hubble rate is needed in the third-order deceleration-distance series in y. -/
theorem dQ_y_third_order_h3 : necessity% Checked.Cosmography.CVdQ.dQ_y_third_order 3 := by
  refine ⟨flatStart, 0, flatStart_smooth _, flatStart_ne, ?_⟩
  unfold Checked.Cosmography.CVdQ.remainderQ Checked.Cosmography.CVdQ.seriesQ
  exact not_littleO_deg2m _ _ _ _ _ _ 3 (by norm_num) flatStart_hubble flatStart_y_tendsto flatStart_y_freq

/-- A nonzero Hubble rate is needed in the fifth-order curved luminosity-distance series in y. -/
theorem lumDist_y_fifth_order_h3 : necessity% Checked.Cosmography.BambaK.lumDist_y_fifth_order 3 := by
  refine ⟨0, flatStart, 0, flatStart_smooth _, flatStart_ne, ?_⟩
  unfold Checked.Cosmography.BambaK.remK Checked.Cosmography.BambaK.seriesY4
  exact not_littleO_deg4 _ _ _ _ _ _ _ _ 5 (by norm_num) flatStart_hubble flatStart_y_tendsto flatStart_y_freq

/-- A nonzero Hubble rate is needed in the fifth-order angular-distance series in y. -/
theorem angDist_y_fifth_order_h3 : necessity% Checked.Cosmography.BambaA.angDist_y_fifth_order 3 := by
  refine ⟨0, flatStart, 0, flatStart_smooth _, flatStart_ne, ?_⟩
  unfold Checked.Cosmography.BambaA.remA
  exact not_littleO_deg4 _ _ _ _ _ _ _ _ 5 (by norm_num) flatStart_hubble flatStart_y_tendsto flatStart_y_freq

/-- A nonzero Hubble rate is needed in the fifth-order luminosity-distance series in z. -/
theorem lumDist_z_fifth_order_h3 : necessity% Checked.Cosmography.BambaZ.lumDist_z_fifth_order 3 := by
  refine ⟨0, flatStart, 0, flatStart_smooth _, flatStart_ne, ?_⟩
  unfold Checked.Cosmography.BambaZ.remLz Checked.Cosmography.BambaZ.seriesZ
  exact not_littleO_deg4 _ _ _ _ _ _ _ _ 5 (by norm_num) flatStart_hubble flatStart_z_tendsto flatStart_z_freq

/-- A nonzero Hubble rate is needed in the fifth-order angular-distance series in z. -/
theorem angDist_z_fifth_order_h3 : necessity% Checked.Cosmography.BambaZ.angDist_z_fifth_order 3 := by
  refine ⟨0, flatStart, 0, flatStart_smooth _, flatStart_ne, ?_⟩
  unfold Checked.Cosmography.BambaZ.remAz Checked.Cosmography.BambaZ.seriesZ
  exact not_littleO_deg4 _ _ _ _ _ _ _ _ 5 (by norm_num) flatStart_hubble flatStart_z_tendsto flatStart_z_freq

end SeriesHubble

end Checked.Trust.NCB
