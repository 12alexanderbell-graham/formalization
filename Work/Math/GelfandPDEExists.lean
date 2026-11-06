import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.ODE.PicardLindelof
import Checked.Math.Gelfand
import Checked.Math.GelfandExists
import Work.Math.RadialLaplacian
import Work.Math.RadialC2
import Work.Math.GProfile

/-!
# Mathematics (THE RESULT part 5): the Gelfand problem in the unit ball of ℝ³ as a PDE —
# existence of radial solutions up to the certified bound

**Question.** Companion of `Work.Math.GelfandPDE.gelfand_pde_radial_bound` (no radial classical
solution of Δu + λ eᵘ = 0 in the unit ball of ℝ³, u = 0 on the sphere, for λ > 3.321992119): for
which λ does a radial classical solution exist? Together the two statements locate the supremum λ*
of the λ with a radial solution in [3.321992118, 3.321992119].

**What is stated here** (frozen before the proof, annex 40.1). For every λ with
0 < λ ≤ 3.321992118 there is u : ℝ³ → ℝ (`EuclideanSpace ℝ (Fin 3)`) that is twice continuously
differentiable on the open unit ball, continuous on the closed unit ball, zero on the unit sphere,
a function of ‖x‖ alone on the closed ball, and solves Δu x + λ e^{u x} = 0 at every x of the open
ball (Δ is Mathlib's Laplacian). The hypotheses of the companion statement are exactly these.

**Not stated here:** λ ≤ 0 (λ = 0 has u = 0; λ < 0 is a different problem); the number of
solutions for each λ; non-radial solutions.

Only Mathlib definitions occur in the statement (no program definition to pin).
-/

namespace Work.Math.GelfandPDEExists
open Set Filter Topology InnerProductSpace Laplacian Metric

/-- C² on an open set from two explicit derivatives with a continuous second one. -/
theorem contDiffOn_two_of_derivs {f f1 f2 : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (h1 : ∀ y ∈ U, HasDerivAt f (f1 y) y) (h2 : ∀ y ∈ U, HasDerivAt f1 (f2 y) y)
    (h3 : ContinuousOn f2 U) : ContDiffOn ℝ 2 f U := by
  have e2 : (2 : WithTop ℕ∞) = 1 + 1 := by norm_num
  rw [e2, contDiffOn_succ_iff_deriv_of_isOpen hU]
  refine ⟨fun y hy => (h1 y hy).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  have hd : EqOn (deriv f) f1 U := fun y hy => (h1 y hy).deriv
  refine (ContDiffOn.congr ?_ hd)
  have e1 : (1 : WithTop ℕ∞) = 0 + 1 := by norm_num
  rw [e1, contDiffOn_succ_iff_deriv_of_isOpen hU]
  refine ⟨fun y hy => (h2 y hy).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  have hd2 : EqOn (deriv f1) f2 U := fun y hy => (h2 y hy).deriv
  exact (contDiffOn_zero.2 h3).congr hd2


/-- Gelfand problem in the unit ball of ℝ³, radial solutions exist: for every λ with
0 < λ ≤ 3.321992118 there is a function u, twice continuously differentiable on the open unit ball,
continuous on the closed unit ball, zero on the unit sphere and a function of ‖x‖ alone on the
closed ball, with Δu + λ eᵘ = 0 at every point of the open ball (Δ is Mathlib's Laplacian). -/
theorem gelfand_pde_radial_exists (lam : ℝ) (hpos : 0 < lam) (hle : lam ≤ 3.321992118) :
    ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
      ContDiffOn ℝ 2 u (ball 0 1) ∧
      ContinuousOn u (closedBall 0 1) ∧
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
      (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖) ∧
      (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0) := by
  obtain ⟨W, Φ, hw, hφ0, hφ, h0⟩ :=
    Checked.Math.GelfandExists.exists_solution (41 / 10) (by norm_num)
  obtain ⟨s₁, hs1lo, hs1hi, -, hlo, -⟩ :=
    Checked.Math.Gelfand.gelfand_ball_critical (41 / 10) le_rfl W Φ hw hφ0 hφ h0
  set S : ℝ := 41 / 10 with hSdef
  have hS : (0 : ℝ) < S := by norm_num
  obtain ⟨hφb, hwb, hDb⟩ := Work.Math.GProfile.profile_bounds S hS W Φ hw hφ0 hφ h0
  have hs1S : s₁ < S := by rw [hSdef]; norm_num at hs1hi ⊢; linarith
  have hs10 : 0 < s₁ := by norm_num at hs1lo; linarith
  have cW : ContinuousOn W (Icc 0 S) := fun t ht => (hw t ht).continuousWithinAt
  have cΛ : ContinuousOn (fun t => t ^ 2 * Real.exp (W t)) (Icc 0 s₁) :=
    ((continuousOn_id.pow 2).mul (cW.rexp)).mono (Icc_subset_Icc le_rfl hs1S.le)
  have hmem : lam ∈ Icc ((fun t => t ^ 2 * Real.exp (W t)) 0)
      ((fun t => t ^ 2 * Real.exp (W t)) s₁) := ⟨by simp; linarith, by simp only; linarith⟩
  obtain ⟨s, hs, hsl⟩ := intermediate_value_Icc hs10.le cΛ hmem
  simp only at hsl
  have hs0 : 0 < s := by
    rcases eq_or_lt_of_le hs.1 with h | h
    · rw [← h] at hsl; simp at hsl; linarith
    · exact h
  have hsS : s < S := lt_of_le_of_lt hs.2 hs1S
  set c : ℝ := Real.log (s ^ 2 / lam) with hc
  have hec : Real.exp c = s ^ 2 / lam := Real.exp_log (by positivity)
  set F : ℝ → ℝ := fun ρ => W (s * ρ) + c with hF
  set F1 : ℝ → ℝ := fun ρ => s * Φ (s * ρ) with hF1d
  set F2 : ℝ → ℝ := fun ρ => s ^ 2 * (-(2 / (s * ρ) * Φ (s * ρ)) - Real.exp (W (s * ρ)))
    with hF2d
  set R : ℝ := S / s with hRd
  have hR1 : 1 < R := (one_lt_div hs0).2 hsS
  have hR0 : 0 < R := by linarith
  have mem : ∀ ρ ∈ Ioo 0 R, s * ρ ∈ Ioo 0 S := fun ρ hρ =>
    ⟨mul_pos hs0 hρ.1, by have := hρ.2; rw [hRd, lt_div_iff₀ hs0] at this; linarith⟩
  have memc : ∀ ρ ∈ Icc 0 R, s * ρ ∈ Icc 0 S := fun ρ hρ =>
    ⟨mul_nonneg hs0.le hρ.1, by have := hρ.2; rw [hRd, le_div_iff₀ hs0] at this; linarith⟩
  have dW : ∀ t ∈ Ioo 0 S, HasDerivAt W (Φ t) t := fun t ht =>
    (hw t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have dΦ : ∀ t ∈ Ioo 0 S, HasDerivAt Φ (-(2 / t * Φ t) - Real.exp (W t)) t := fun t ht =>
    (hφ t ⟨ht.1, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hF1 : ∀ ρ ∈ Ioo 0 R, HasDerivAt F (F1 ρ) ρ := by
    intro ρ hρ
    have h := ((dW _ (mem ρ hρ)).comp ρ ((hasDerivAt_id ρ).const_mul s)).add_const c
    convert h using 1
    all_goals first | rfl | (simp only [hF1d, Function.comp_def, id]; ring)
  have hF2 : ∀ ρ ∈ Ioo 0 R, HasDerivAt F1 (F2 ρ) ρ := by
    intro ρ hρ
    have h := ((dΦ _ (mem ρ hρ)).comp ρ ((hasDerivAt_id ρ).const_mul s)).const_mul s
    convert h using 1
    all_goals first | rfl | (simp only [hF2d, Function.comp_def, id]; ring)
  have cΦ : ∀ t ∈ Ioo 0 S, ContinuousAt Φ t := fun t ht => (dΦ t ht).continuousAt
  have hF2c : ContinuousOn F2 (Ioo 0 R) := by
    intro ρ hρ
    have hm := mem ρ hρ
    have ct : ContinuousAt (fun ρ : ℝ => s * ρ) ρ := (continuous_const.mul continuous_id).continuousAt
    have c1 : ContinuousAt (fun ρ => Φ (s * ρ)) ρ := (cΦ _ hm).comp ct
    have c2 : ContinuousAt (fun ρ => W (s * ρ)) ρ := (dW _ hm).continuousAt.comp ct
    exact (continuousAt_const.mul (((continuousAt_const.div ct hm.1.ne').mul c1).neg.sub
      c2.rexp)).continuousWithinAt
  -- bounds at the centre
  set L : ℝ := -(s ^ 2 / 3) with hL
  set C : ℝ := s ^ 4 * R + s ^ 2 with hC
  have key : ∀ t ∈ Ioo 0 S, |Φ t / t + 1 / 3| ≤ t ^ 2 ∧
      |3 * (Φ t / t) + Real.exp (W t)| ≤ t ^ 2 / 15 := by
    intro t ht
    have htc : t ∈ Icc 0 S := ⟨ht.1.le, ht.2.le⟩
    have hA := hDb t htc
    have hwl := (hwb t htc).1
    have hwu := (hwb t htc).2
    have he1 : Real.exp (W t) ≤ 1 := Real.exp_le_one_iff.2 hwu
    have he2 : 1 + W t ≤ Real.exp (W t) := by linarith [Real.add_one_le_exp (W t)]
    have ht0 : 0 < t := ht.1
    have ht3 : 0 < t ^ 3 := by positivity
    have eA : 3 * (Φ t / t) + Real.exp (W t) =
        (3 * (t ^ 2 * Φ t) + t ^ 3 * Real.exp (W t)) / t ^ 3 := by
      field_simp
    have b2 : |3 * (Φ t / t) + Real.exp (W t)| ≤ t ^ 2 / 15 := by
      rw [eA, abs_div, abs_of_pos ht3, div_le_iff₀ ht3]
      calc _ ≤ t ^ 5 / 15 := hA
        _ = t ^ 2 / 15 * t ^ 3 := by ring
    refine ⟨?_, b2⟩
    have e1 : Φ t / t + 1 / 3 = (3 * (Φ t / t) + Real.exp (W t)) / 3 +
        (1 - Real.exp (W t)) / 3 := by ring
    rw [e1]
    have b3 : |(1 - Real.exp (W t)) / 3| ≤ t ^ 2 / 18 := by
      rw [abs_div, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - Real.exp (W t))]
      norm_num <;> linarith
    have b4 : |(3 * (Φ t / t) + Real.exp (W t)) / 3| ≤ t ^ 2 / 45 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3), div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
      linarith [b2]
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ t ^ 2 / 45 + t ^ 2 / 18 := add_le_add b4 b3
      _ ≤ t ^ 2 := by nlinarith [sq_nonneg t]
  have hs4 : 0 ≤ s ^ 4 * R := by positivity
  have hM : ∀ ρ ∈ Ioo 0 R, |F1 ρ / ρ - L| ≤ C * ρ := by
    intro ρ hρ
    have hm := mem ρ hρ
    have k := (key _ hm).1
    have hρ0 : 0 < ρ := hρ.1
    have e : F1 ρ / ρ - L = s ^ 2 * (Φ (s * ρ) / (s * ρ) + 1 / 3) := by
      simp only [hF1d, hL]; field_simp; ring
    rw [e, abs_mul, abs_of_nonneg (by positivity)]
    calc s ^ 2 * |Φ (s * ρ) / (s * ρ) + 1 / 3| ≤ s ^ 2 * (s * ρ) ^ 2 :=
          mul_le_mul_of_nonneg_left k (by positivity)
      _ = s ^ 4 * ρ * ρ := by ring
      _ ≤ s ^ 4 * R * ρ := by
          apply mul_le_mul_of_nonneg_right _ hρ0.le
          exact mul_le_mul_of_nonneg_left hρ.2.le (by positivity)
      _ ≤ C * ρ := by
          apply mul_le_mul_of_nonneg_right _ hρ0.le
          simp only [hC]; nlinarith [sq_nonneg s]
  have hK : ∀ ρ ∈ Ioo 0 R, |F2 ρ - F1 ρ / ρ| ≤ C * ρ := by
    intro ρ hρ
    have hm := mem ρ hρ
    have k := (key _ hm).2
    have hρ0 : 0 < ρ := hρ.1
    have e : F2 ρ - F1 ρ / ρ = -(s ^ 2 * (3 * (Φ (s * ρ) / (s * ρ)) + Real.exp (W (s * ρ)))) := by
      simp only [hF1d, hF2d]; field_simp; ring
    rw [e, abs_neg, abs_mul, abs_of_nonneg (by positivity)]
    calc s ^ 2 * |3 * (Φ (s * ρ) / (s * ρ)) + Real.exp (W (s * ρ))| ≤ s ^ 2 * ((s * ρ) ^ 2 / 15) :=
          mul_le_mul_of_nonneg_left k (by positivity)
      _ ≤ s ^ 4 * ρ * ρ := by nlinarith [sq_nonneg (s * ρ), sq_nonneg s, sq_nonneg ρ]
      _ ≤ s ^ 4 * R * ρ := by
          apply mul_le_mul_of_nonneg_right _ hρ0.le
          exact mul_le_mul_of_nonneg_left hρ.2.le (by positivity)
      _ ≤ C * ρ := by
          apply mul_le_mul_of_nonneg_right _ hρ0.le
          simp only [hC]; nlinarith [sq_nonneg s]
  have hquad : ∀ ρ ∈ Ico 0 R, |F ρ - F 0| ≤ C * ρ ^ 2 := by
    intro ρ hρ
    have hm := memc ρ ⟨hρ.1, hρ.2.le⟩
    have b := hwb _ hm
    have e : F ρ - F 0 = W (s * ρ) := by simp [hF, h0]
    rw [e, abs_of_nonpos b.2]
    have : -W (s * ρ) ≤ s ^ 2 * ρ ^ 2 / 6 := by have := b.1; nlinarith
    calc -W (s * ρ) ≤ s ^ 2 * ρ ^ 2 / 6 := this
      _ ≤ C * ρ ^ 2 := by
          simp only [hC]; nlinarith [sq_nonneg ρ, sq_nonneg s, mul_nonneg hs4 (sq_nonneg ρ)]
  -- the solution
  refine ⟨fun x => F ‖x‖, ?_, ?_, ?_, ⟨F, fun x _ => rfl⟩, ?_⟩
  · intro x hx
    rw [mem_ball_zero_iff] at hx
    refine ContDiffAt.contDiffWithinAt ?_
    by_cases hx0 : x = 0
    · subst hx0
      exact Work.Math.RadialC2.contDiffAt_zero_radial hR0 hF1 hF2 hF2c hM hK hquad
    · have hr : ‖x‖ ∈ Ioo 0 R := ⟨norm_pos_iff.2 hx0, by linarith⟩
      have hFc : ContDiffOn ℝ 2 F (Ioo 0 R) := contDiffOn_two_of_derivs isOpen_Ioo hF1 hF2 hF2c
      exact (hFc.contDiffAt (isOpen_Ioo.mem_nhds hr)).comp x (contDiffAt_norm ℝ hx0)
  · have cF : ContinuousOn F (Icc 0 1) := by
      have : ContinuousOn (fun ρ => W (s * ρ)) (Icc 0 1) :=
        cW.comp (continuous_const.mul continuous_id).continuousOn
          (fun ρ hρ => memc ρ ⟨hρ.1, hρ.2.trans hR1.le⟩)
      exact this.add continuousOn_const
    exact cF.comp continuous_norm.continuousOn (fun x hx =>
      ⟨norm_nonneg x, mem_closedBall_zero_iff.1 hx⟩)
  · intro x hx
    simp only [hF, hx, mul_one]
    rw [← Real.exp_eq_one_iff, Real.exp_add, hec]
    field_simp
    linarith [hsl]
  · intro x hx
    rw [mem_ball_zero_iff] at hx
    by_cases hx0 : x = 0
    · subst hx0
      rw [Work.Math.RadialC2.laplacian_radial_zero hR0 hF1 hF2 hM hquad, finrank_euclideanSpace_fin]
      simp only [norm_zero, hF, mul_zero, h0, zero_add, hec, hL]
      field_simp
      norm_num
    · have hr : ‖x‖ ∈ Ioo 0 R := ⟨norm_pos_iff.2 hx0, by linarith⟩
      have hL' := Work.Math.RadialLaplacian.laplacian_radial (f := F) (f' := F1)
        (f'' := F2 ‖x‖) hx0
        (by filter_upwards [isOpen_Ioo.mem_nhds hr] with ρ hρ using hF1 ρ hρ)
        (hF2 _ hr)
      rw [hL', finrank_euclideanSpace_fin]
      have hr0 : 0 < ‖x‖ := hr.1
      simp only [hF, hF1d, hF2d, Real.exp_add, hec]
      field_simp
      ring

end Work.Math.GelfandPDEExists
