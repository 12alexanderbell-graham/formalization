import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Order.IntermediateValue
import Checked.FSSep.SAssemble
import Checked.FSSep.SSlowHi

/-! Falkner–Skan separation, a slow-approach trajectory from a zero wall value: the scaled clamped flow with
the slow-approach event solves the pressure-gradient form with zero wall shear, the velocity profile tends to
the edge value and the second derivative is positive beyond the wall (no faster-than-every-exponential claim).
Used for the necessity of the decay hypotheses of the separation equality theorem. -/

namespace Checked.FSSep.SSlowSol
open Set Filter Topology Checked.FSNeg.NBase Checked.FSSep.SBase Checked.FSSep.SFlow Checked.FSSep.SAssemble

theorem slow_sol {K : ℝ} (hK5 : 5 ≤ K) (hS : SlowS (flowK K)) :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-(1 / K)) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ q 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ioi (0 : ℝ), 0 < q η) := by
  have hK : 0 < K := by linarith
  obtain ⟨η₀, hη₀, hpre, hs1, hs2, hs3⟩ := hS
  have U := slow_unclamp hK5 hη₀ hpre hs1 hs2 hs3
  obtain ⟨hF, hP, hQ⟩ := comps K
  set F := fun t => (flowK K t).1
  set P := fun t => (flowK K t).2.1
  set Q := fun t => (flowK K t).2.2
  have h0 := flowK_zero K
  have hF0 : F 0 = 0 := by simp [F, h0]
  have hP0 : P 0 = 0 := by simp [P, h0]
  have hQ0 : Q 0 = 0 := by simp [Q, h0]
  have ceq := @Checked.FSSep.SUnclamp.cl_eq
  have tF : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt F (P η) (Ici 0) η := fun η hη => by
    have u := U η hη
    have := hF η hη; rwa [ceq (by linarith [u.1]) (by linarith [u.2.1])] at this
  have tP : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt P (Q η) (Ici 0) η := fun η hη => by
    have u := U η hη
    have := hP η hη; rwa [ceq (by linarith [u.2.2.1]) (by linarith [u.2.2.2.2.1])] at this
  have tQ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt Q (-(K * F η * Q η) + 1 - P η ^ 2) (Ici 0) η :=
    fun η hη => by
    have u := U η hη
    have hη0 : (0 : ℝ) ≤ η := hη
    have := hQ η hη
    rwa [ceq (c := max η 0 + 2) (y := F η) (by rw [max_eq_left hη0]; linarith [u.2.2.2.2.2.1])
        (by rw [max_eq_left hη0]; linarith [u.2.2.2.2.2.2.1]),
      ceq (c := 2) (y := Q η) (by linarith [u.2.2.1]) (by linarith [u.2.2.2.2.1]),
      ceq (c := 2) (y := P η) (by linarith [u.1]) (by linarith [u.2.1])] at this
  have hqpos : ∀ η ∈ Ioi (0 : ℝ), 0 < Q η := fun η hη =>
    (U η (le_of_lt (show (0 : ℝ) < η from hη))).2.2.2.1 hη
  have hlim : Tendsto P atTop (𝓝 1) :=
    Checked.FSNeg.NLimit.neg_limit hK tF tP tQ (a := 1) (by norm_num)
      (fun η hη => hqpos η (show (0 : ℝ) < η from lt_of_lt_of_le one_pos hη))
      (by linarith [(U 1 (by norm_num)).1])
      (fun η hη => (U η (show (0 : ℝ) ≤ η from le_trans zero_le_one hη)).2.1)
  have hc : 0 < Real.sqrt K := Real.sqrt_pos.2 hK
  have hc2 : Real.sqrt K ^ 2 = K := Real.sq_sqrt hK.le
  have tQ' : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt Q (-(K * F η * Q η) - (-1) * (1 - P η ^ 2)) (Ici 0) η :=
    fun η hη => (tQ η hη).congr_deriv (by ring)
  obtain ⟨A, B, C⟩ := Checked.FalknerSkan.FSScale.scale hc tF tP tQ'
  refine ⟨fun s => Real.sqrt K * F (s / Real.sqrt K), fun s => P (s / Real.sqrt K),
    fun s => Q (s / Real.sqrt K) / Real.sqrt K, A, B, fun s hs => ?_, by simp [hF0],
    by simp [hP0], by simp [hQ0], Checked.FalknerSkan.FSScale.scale_lim hc hlim,
    fun s hs => div_pos (hqpos _ (div_pos hs hc)) hc⟩
  refine (C s hs).congr_deriv ?_
  rw [hc2]
  field_simp

/-- The certified slow-approach chain at the upper coefficient gives a zero-wall-shear solution of the
pressure-gradient form with the upper window end as parameter. -/
theorem slow_hi :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q
        (-(f η * q η) - (-(1988377350 / 10000000000 : ℝ)) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ q 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ioi (0 : ℝ), 0 < q η) := by
  have h := slow_sol (K := 10000000000 / 1988377350) (by norm_num)
    (of_chain Checked.FSSep.SSlowHi.chain)
  have e : (-(1 / (10000000000 / 1988377350 : ℝ))) = -(1988377350 / 10000000000 : ℝ) := by norm_num
  rw [e] at h
  exact h

end Checked.FSSep.SSlowSol
