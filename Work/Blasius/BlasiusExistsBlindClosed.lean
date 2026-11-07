import Mathlib
import Work.Blasius.BlasiusBlind
import Work.Blasius.BlasiusExists

/-!
# Blasius existence: the blind restatement, closed

The blind restater's `Blind.Blasius.exists_blasius_solution` (run 2026-11-07T1228Z: f is C³ on
[0, ∞) and solves f''' + (1/2) f f'' = 0 with one-sided `derivWithin` on [0, ∞), f(0) = 0,
f'(0) = 0, f' → 1) follows from the program's frozen `Work.Blasius.blasius_exists`: along
[0, ∞) the iterated `derivWithin` of f agree with p and q, and C³ follows from
`contDiffOn_succ_iff_derivWithin` three times.
-/

namespace Work.Blasius.BlindClosed
open Set Filter Topology

theorem exists_blasius_solution : ∃ f : ℝ → ℝ, Blind.Blasius.IsBlasiusSolution f := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim⟩ := Work.Blasius.blasius_exists
  have hU : UniqueDiffOn ℝ (Ici (0 : ℝ)) := uniqueDiffOn_Ici 0
  have e1 : EqOn (derivWithin f (Ici 0)) p (Ici 0) := fun η hη => (hf η hη).derivWithin (hU η hη)
  have e2 : EqOn (derivWithin (derivWithin f (Ici 0)) (Ici 0)) q (Ici 0) := fun η hη => by
    rw [derivWithin_congr e1 (e1 hη)]; exact (hp η hη).derivWithin (hU η hη)
  have e3 : ∀ η ∈ Ici (0 : ℝ), derivWithin (derivWithin (derivWithin f (Ici 0)) (Ici 0)) (Ici 0) η
      = -(f η * q η / 2) := fun η hη => by
    rw [derivWithin_congr e2 (e2 hη)]; exact (hq η hη).derivWithin (hU η hη)
  have cf : ContinuousOn f (Ici 0) := fun η hη => (hf η hη).continuousWithinAt
  have cq : ContinuousOn q (Ici 0) := fun η hη => (hq η hη).continuousWithinAt
  have dq : DifferentiableOn ℝ q (Ici 0) := fun η hη => (hq η hη).differentiableWithinAt
  have dp : DifferentiableOn ℝ p (Ici 0) := fun η hη => (hp η hη).differentiableWithinAt
  have df : DifferentiableOn ℝ f (Ici 0) := fun η hη => (hf η hη).differentiableWithinAt
  have C0 : ContDiffOn ℝ 0 (fun η => -(f η * q η / 2)) (Ici 0) :=
    contDiffOn_zero.2 ((cf.mul cq).div_const 2).neg
  have C1 : ContDiffOn ℝ 1 q (Ici 0) := by
    refine (contDiffOn_succ_iff_derivWithin (n := 0) hU).2 ⟨dq, by simp, ?_⟩
    exact C0.congr fun η hη => ((hq η hη).derivWithin (hU η hη))
  have C2 : ContDiffOn ℝ 2 p (Ici 0) := by
    refine (contDiffOn_succ_iff_derivWithin (n := 1) hU).2 ⟨dp, by simp, ?_⟩
    exact C1.congr fun η hη => ((hp η hη).derivWithin (hU η hη))
  have C3 : ContDiffOn ℝ 3 f (Ici 0) := by
    refine (contDiffOn_succ_iff_derivWithin (n := 2) hU).2 ⟨df, by simp, ?_⟩
    exact C2.congr e1
  refine ⟨f, C3, fun η hη => ?_, hf0, ?_, ?_⟩
  · rw [e3 η hη, e2 hη]; ring
  · rw [e1 (show (0 : ℝ) ∈ Ici 0 from mem_Ici.2 le_rfl)]; exact hp0
  · refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (e1 (mem_Ici.2 ht)).symm

end Work.Blasius.BlindClosed
