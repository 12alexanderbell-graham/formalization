import Mathlib

/-!
# Robertson's stiff network at t = 40: blind restatement

Written by a blind restater (Sonnet, run 2026-11-06T0428Z) from the scientific source alone
(`runs/2026-11-06T0428Z/blind/RobBlind.lean`), copied verbatim except the namespace; its two
theorem statements `blind_state40` and `blind_exists` are proved, with the same statements, in
`Work.Sim.RobAudit` from the program's frozen theorems.
-/

namespace Work.Sim.RobBlind

/-- `Solves y₁ y₂ y₃ T`: the triple solves Robertson's mass-action rate equations on `[0,T]`
with initial data (1,0,0).
Reactions: A→B (0.04), B+C→A+C (10^4), 2B→C+B (3·10^7), giving
 A' = -0.04 A + 10^4 B C
 B' =  0.04 A - 10^4 B C - 3·10^7 B²
 C' =  3·10^7 B²
(2B→C+B: net B -1, C +1, rate 3·10^7 B².)
Weakest reading: continuity on the closed interval, and the ODE (two-sided derivative) only on
the open interior (0,T). One-sided derivatives at endpoints then follow from continuity of the
right-hand side, so nothing is lost, and a hypothesis that is weaker makes the uniqueness-style
claim `blind_state40` stronger. -/
def Solves (y₁ y₂ y₃ : ℝ → ℝ) (T : ℝ) : Prop :=
  ContinuousOn y₁ (Set.Icc 0 T) ∧ ContinuousOn y₂ (Set.Icc 0 T) ∧ ContinuousOn y₃ (Set.Icc 0 T) ∧
  y₁ 0 = 1 ∧ y₂ 0 = 0 ∧ y₃ 0 = 0 ∧
  ∀ t ∈ Set.Ioo 0 T,
    HasDerivAt y₁ (-(4/100 : ℝ) * y₁ t + 10000 * y₂ t * y₃ t) t ∧
    HasDerivAt y₂ ((4/100 : ℝ) * y₁ t - 10000 * y₂ t * y₃ t - 30000000 * (y₂ t)^2) t ∧
    HasDerivAt y₃ (30000000 * (y₂ t)^2) t

end Work.Sim.RobBlind
