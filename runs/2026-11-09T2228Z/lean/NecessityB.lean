import Checked.Trust.NonVacuity
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
* rigorous simulation headlines: the solution hypothesis (the zero functions).
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
  refine Checked.Townes.Shooting.townes_under S θ φ hS h1 ?_ h3 h4
  exact cont_at_zero_of_continuous S (by linarith) 0 θ φ (fun y => y - y ^ 3) (by fun_prop) h1
    (fun ξ hξ => (h3 ξ hξ).congr_deriv (by push_cast; ring))

theorem townes_over_r3 : dropped% Checked.Townes.Shooting.townes_over 3 := by
  intro S hS θ φ h1 h3 h4
  refine Checked.Townes.Shooting.townes_over S θ φ hS h1 ?_ h3 h4
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
    field_simp
    ring
  · rintro ⟨h, -⟩
    norm_num at h

theorem fs_zero_wall_shear_h1 : necessity% Checked.FalknerSkan.fs_zero_wall_shear 1 := by
  obtain ⟨h2, h3, h6⟩ := ratProfile
  refine ⟨fun η => 6 * η * (1 + η) / ((1 + 2 * η) * (1 + η + η ^ 2)),
    fun η => 1 - (1 + η + η ^ 2)⁻¹, fun η => (1 + 2 * η) / (1 + η + η ^ 2) ^ 2,
    h2, fun η hη => (h3 η hη).congr_deriv ?_, by norm_num, by norm_num, h6, ?_⟩
  · have h0 : 0 < 1 + η + η ^ 2 := by have := mem_Ici.mp hη; positivity
    have h1 : 0 < 1 + 2 * η := by have := mem_Ici.mp hη; linarith
    field_simp
    ring
  · rintro ⟨h, -⟩
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
  obtain ⟨η, hη, hp1, hqpos⟩ := Checked.Hiemenz.hiemenz_over 15 / 2 le_rfl f p q hf hp hq hf0 hp0 hq0
  rintro ⟨η', hη', hq', hp'⟩
  rcases le_or_gt η' η with h | h
  · exact absurd hq' (not_lt.2 (hqpos η' ⟨hη'.1.le, h⟩).le)
  · exact absurd hp1 (not_lt.2 (hp' η ⟨hη.1.le, h.le⟩).le)

/-- The initial wall shear is needed: the certified solution with the other end of the bracket
undershoots, so it cannot overshoot. -/
theorem hiemenz_over_h7 : necessity% Checked.Hiemenz.hiemenz_over 7 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hq0⟩ := Checked.Hiemenz.HIVP.ivp_lo
  refine ⟨15 / 2, le_rfl, f, p, q, hf, hp, hq, hf0, hp0, ?_⟩
  obtain ⟨η, hη, hqneg, hp1⟩ := Checked.Hiemenz.hiemenz_under 15 / 2 le_rfl f p q hf hp hq hf0 hp0 hq0
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
    ring
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

end Checked.Trust.NCB
