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

/-! Gelfand PDE, `GProfile`: elementary bounds on the scaled Gelfand profile near the centre (monotonicity only). Promoted from `Work/Math/GProfile.lean`. -/

namespace Checked.Math.GProfile
open Set Filter Topology

theorem profile_bounds (S : ℝ) (hS : 0 < S) (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt w (φ s) (Icc 0 S) s)
    (hφ0 : ContinuousWithinAt φ (Icc 0 S) 0)
    (hφ : ∀ s ∈ Ioc (0 : ℝ) S,
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 S) s)
    (h0 : w 0 = 0) :
    (∀ t ∈ Icc (0 : ℝ) S, -(t / 3) ≤ φ t ∧ φ t ≤ 0) ∧
    (∀ t ∈ Icc (0 : ℝ) S, -(t ^ 2 / 6) ≤ w t ∧ w t ≤ 0) ∧
    (∀ t ∈ Icc (0 : ℝ) S, |3 * (t ^ 2 * φ t) + t ^ 3 * Real.exp (w t)| ≤ t ^ 5 / 15) := by
  have h0S : (0 : ℝ) ∈ Icc 0 S := ⟨le_rfl, hS.le⟩
  have cφ : ContinuousOn φ (Icc 0 S) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h]; exact hφ0
    · exact (hφ t ⟨h, ht.2⟩).continuousWithinAt
  have cw : ContinuousOn w (Icc 0 S) := fun t ht => (hw t ht).continuousWithinAt
  have io : ∀ t ∈ interior (Icc (0 : ℝ) S), t ∈ Ioc (0 : ℝ) S ∧ t ∈ Icc (0 : ℝ) S := by
    intro t ht; rw [interior_Icc] at ht; exact ⟨⟨ht.1, ht.2.le⟩, ⟨ht.1.le, ht.2.le⟩⟩
  -- q = t² φ
  set q : ℝ → ℝ := fun t => t ^ 2 * φ t with hq
  have dq : ∀ t ∈ Ioc (0 : ℝ) S,
      HasDerivWithinAt q (-(t ^ 2 * Real.exp (w t))) (Icc 0 S) t := by
    intro t ht
    have h := ((hasDerivAt_pow 2 t).hasDerivWithinAt (s := Icc 0 S)).mul (hφ t ht)
    convert h using 1
    have : t ≠ 0 := ht.1.ne'
    field_simp
    ring
  have cq : ContinuousOn q (Icc 0 S) := (continuousOn_id.pow 2).mul cφ
  have q0 : q 0 = 0 := by simp [hq]
  have qanti : AntitoneOn q (Icc 0 S) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 S) cq
      (fun t ht => ((dq t (io t ht).1).mono interior_subset))
      (fun t ht => by
        have := Real.exp_pos (w t)
        have : 0 ≤ t ^ 2 * Real.exp (w t) := by positivity
        linarith)
  have qle : ∀ t ∈ Icc (0 : ℝ) S, q t ≤ 0 := fun t ht => by
    have := qanti h0S ht ht.1; rwa [q0] at this
  -- φ ≤ 0 on (0, S], then at 0 by continuity
  have φle' : ∀ t ∈ Ioc (0 : ℝ) S, φ t ≤ 0 := fun t ht => by
    have h := qle t ⟨ht.1.le, ht.2⟩
    have ht2 : 0 < t ^ 2 := by have := ht.1; positivity
    simp only [hq] at h
    by_contra hc; push_neg at hc; nlinarith [mul_pos ht2 hc]
  haveI hne : (𝓝[Ioc (0 : ℝ) S] (0 : ℝ)).NeBot := left_nhdsWithin_Ioc_neBot hS
  have tφ : Tendsto φ (𝓝[Ioc (0 : ℝ) S] 0) (𝓝 (φ 0)) :=
    (hφ0.mono Ioc_subset_Icc_self).tendsto
  have φ0le : φ 0 ≤ 0 :=
    le_of_tendsto tφ (eventually_nhdsWithin_of_forall fun t ht => φle' t ht)
  have φle : ∀ t ∈ Icc (0 : ℝ) S, φ t ≤ 0 := fun t ht => by
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h]; exact φ0le
    · exact φle' t ⟨h, ht.2⟩
  -- w ≤ 0
  have wanti : AntitoneOn w (Icc 0 S) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 S) cw
      (fun t ht => ((hw t (io t ht).2).mono interior_subset))
      (fun t ht => φle t (io t ht).2)
  have wle : ∀ t ∈ Icc (0 : ℝ) S, w t ≤ 0 := fun t ht => by
    have := wanti h0S ht ht.1; rwa [h0] at this
  have ewle : ∀ t ∈ Icc (0 : ℝ) S, Real.exp (w t) ≤ 1 := fun t ht =>
    Real.exp_le_one_iff.2 (wle t ht)
  -- q ≥ −t³/3
  have qmono : MonotoneOn (fun t => q t + t ^ 3 / 3) (Icc 0 S) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 S)
      (cq.add ((continuousOn_id.pow 3).div_const 3))
      (fun t ht => (((dq t (io t ht).1).add
        (((hasDerivAt_pow 3 t).div_const 3).hasDerivWithinAt)).mono interior_subset))
    intro t ht
    have := ewle t (io t ht).2
    have : t ^ 2 * Real.exp (w t) ≤ t ^ 2 := by nlinarith [sq_nonneg t]
    simp only [Nat.cast_ofNat]
    nlinarith
  have qge : ∀ t ∈ Icc (0 : ℝ) S, -(t ^ 3 / 3) ≤ q t := fun t ht => by
    have := qmono h0S ht ht.1
    simp only [q0] at this
    norm_num at this
    linarith
  have φge' : ∀ t ∈ Ioc (0 : ℝ) S, -(t / 3) ≤ φ t := fun t ht => by
    have h := qge t ⟨ht.1.le, ht.2⟩
    have ht2 : 0 < t ^ 2 := by have := ht.1; positivity
    simp only [hq] at h
    by_contra hc; push_neg at hc
    have : t ^ 2 * φ t < t ^ 2 * (-(t / 3)) := mul_lt_mul_of_pos_left hc ht2
    nlinarith
  have φge : ∀ t ∈ Icc (0 : ℝ) S, -(t / 3) ≤ φ t := fun t ht => by
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h]
      have : (0 : ℝ) ≤ φ 0 := by
        have hl : Tendsto (fun t => -(t / 3)) (𝓝[Ioc (0 : ℝ) S] 0) (𝓝 (-(0 / 3))) :=
          ((continuous_id.div_const 3).neg.tendsto 0).mono_left nhdsWithin_le_nhds
        have := le_of_tendsto_of_tendsto hl tφ
          (eventually_nhdsWithin_of_forall fun t ht => φge' t ht)
        simpa using this
      linarith
    · exact φge' t ⟨h, ht.2⟩
  -- w ≥ −t²/6
  have wmono : MonotoneOn (fun t => w t + t ^ 2 / 6) (Icc 0 S) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 S)
      (cw.add ((continuousOn_id.pow 2).div_const 6))
      (fun t ht => (((hw t (io t ht).2).add
        (((hasDerivAt_pow 2 t).div_const 6).hasDerivWithinAt)).mono interior_subset))
    intro t ht
    have := φge t (io t ht).2
    simp only [Nat.cast_ofNat]
    linarith
  have wge : ∀ t ∈ Icc (0 : ℝ) S, -(t ^ 2 / 6) ≤ w t := fun t ht => by
    have := wmono h0S ht ht.1
    simp only [h0] at this
    norm_num at this
    linarith
  -- D = 3q + t³ eʷ
  set D : ℝ → ℝ := fun t => 3 * q t + t ^ 3 * Real.exp (w t) with hD
  have dD : ∀ t ∈ Ioc (0 : ℝ) S,
      HasDerivWithinAt D (t ^ 3 * Real.exp (w t) * φ t) (Icc 0 S) t := by
    intro t ht
    have h := ((dq t ht).const_mul 3).add
      (((hasDerivAt_pow 3 t).hasDerivWithinAt (s := Icc 0 S)).mul
        ((hw t ⟨ht.1.le, ht.2⟩).exp))
    convert h using 1
    simp only [Nat.cast_ofNat]
    ring
  have cD : ContinuousOn D (Icc 0 S) :=
    (cq.const_smul (3 : ℝ)).add ((continuousOn_id.pow 3).mul (cw.rexp))
  have D0 : D 0 = 0 := by simp [hD, q0]
  have dbound : ∀ t ∈ Icc (0 : ℝ) S, |t ^ 3 * Real.exp (w t) * φ t| ≤ t ^ 4 / 3 := by
    intro t ht
    have h1 := φge t ht; have h2 := φle t ht; have h3 := ewle t ht
    have h4 := Real.exp_pos (w t)
    have ht3 : 0 ≤ t ^ 3 := by have := ht.1; positivity
    rw [abs_mul, abs_mul, abs_of_nonneg ht3, abs_of_pos h4, abs_of_nonpos h2]
    have : -φ t ≤ t / 3 := by linarith
    have h5 : t ^ 3 * Real.exp (w t) ≤ t ^ 3 := by nlinarith
    calc t ^ 3 * Real.exp (w t) * -φ t ≤ t ^ 3 * (t / 3) :=
          mul_le_mul h5 this (by linarith) ht3
      _ = t ^ 4 / 3 := by ring
  have Dup : MonotoneOn (fun t => t ^ 5 / 15 - D t) (Icc 0 S) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 S)
      (((continuousOn_id.pow 5).div_const 15).sub cD)
      (fun t ht => ((((hasDerivAt_pow 5 t).div_const 15).hasDerivWithinAt.sub
        (dD t (io t ht).1)).mono interior_subset))
    intro t ht
    have := (abs_le.1 (dbound t (io t ht).2)).2
    simp only [Nat.cast_ofNat]
    have e : (5 : ℝ) * t ^ 4 / 15 = t ^ 4 / 3 := by ring
    linarith
  have Dlo : MonotoneOn (fun t => t ^ 5 / 15 + D t) (Icc 0 S) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 S)
      (((continuousOn_id.pow 5).div_const 15).add cD)
      (fun t ht => ((((hasDerivAt_pow 5 t).div_const 15).hasDerivWithinAt.add
        (dD t (io t ht).1)).mono interior_subset))
    intro t ht
    have := (abs_le.1 (dbound t (io t ht).2)).1
    simp only [Nat.cast_ofNat]
    have e : (5 : ℝ) * t ^ 4 / 15 = t ^ 4 / 3 := by ring
    linarith
  refine ⟨fun t ht => ⟨φge t ht, φle t ht⟩, fun t ht => ⟨wge t ht, wle t ht⟩, fun t ht => ?_⟩
  have a := Dup h0S ht ht.1
  have b := Dlo h0S ht ht.1
  simp only [D0] at a b
  norm_num at a b
  rw [abs_le]
  exact ⟨by simp only [hD] at b; linarith, by simp only [hD] at a; linarith⟩

end Checked.Math.GProfile
