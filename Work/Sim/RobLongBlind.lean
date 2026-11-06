import Mathlib

/-!
# Robertson's stiff network at t = 10¹¹: blind restatement

Written by a blind restater (Sonnet, run 2026-11-06T0828Z) from the scientific description alone
(`runs/2026-11-06T0828Z/blind/RobLongBlind.lean`), copied verbatim except the namespace; its three
statements are proved, with the same statements, in `Work.Sim.RobLongAudit` from the program's
frozen theorems.
-/

namespace Work.Sim.RobLongBlind

/-- `(y1,y2,y3)` solves the Robertson IVP on `[0,T]`.  Weakest reasonable notion:
each component is continuous on the closed interval `[0,T]`, satisfies the ODE system
with two-sided derivatives at every interior point `t ∈ (0,T)`, and has the initial
values at `0`.  No differentiability at the endpoints is demanded, so claims 1 and 2
(universal over solutions) are as strong as possible; the true classical solution
satisfies this, so existence (claim 3) remains true and faithful. -/
def IsSol (T : ℝ) (y1 y2 y3 : ℝ → ℝ) : Prop :=
  ContinuousOn y1 (Set.Icc 0 T) ∧ ContinuousOn y2 (Set.Icc 0 T) ∧
  ContinuousOn y3 (Set.Icc 0 T) ∧
  y1 0 = 1 ∧ y2 0 = 0 ∧ y3 0 = 0 ∧
  (∀ t ∈ Set.Ioo 0 T,
    HasDerivAt y1 (-(1/25) * y1 t + 10000 * y2 t * y3 t) t ∧
    HasDerivAt y2 ((1/25) * y1 t - 10000 * y2 t * y3 t - 30000000 * (y2 t)^2) t ∧
    HasDerivAt y3 (30000000 * (y2 t)^2) t)

theorem blind_state1e11 (y1 y2 y3 : ℝ → ℝ) (h : IsSol (10^11) y1 y2 y3) :
    (20833401494/10^18 : ℝ) < y1 (10^11) ∧ y1 (10^11) < 20833401500/10^18 ∧
    (83333/10^18 : ℝ) < y2 (10^11) ∧ y2 (10^11) < 83334/10^18 ∧
    (99999997916651/10^14 : ℝ) < y3 (10^11) ∧ y3 (10^11) < 99999997916652/10^14 := by
  sorry

theorem blind_y3_printed_false (y1 y2 y3 : ℝ → ℝ) (h : IsSol (10^11) y1 y2 y3) :
    y3 (10^11) ≠ 9999999791665050/10^16 := by
  sorry

theorem blind_exists1e11 : ∃ y1 y2 y3 : ℝ → ℝ, IsSol (10^11) y1 y2 y3 := by
  sorry

end Work.Sim.RobLongBlind
