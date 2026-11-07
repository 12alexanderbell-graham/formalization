/-! Positive control (annex 39.6), run 2026-11-07T0428Z, throwaway branch only: CI must fail on this. -/
axiom control_bad_axiom_20261107 : (1 : Nat) = 2
theorem control_false_claim_20261107 : (1 : Nat) = 2 := by sorry
theorem control_uses_axiom_20261107 : (1 : Nat) = 2 := control_bad_axiom_20261107
