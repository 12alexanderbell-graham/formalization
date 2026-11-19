/-! Planted control for the nanoda judge (run 2026-11-19T2028Z): a few core-only declarations whose export,
checked by nanoda, must pass; a copy with one literal changed must fail. -/
theorem ndctl_a : 2 + 2 = 4 := rfl
theorem ndctl_b (n : Nat) : n + 0 = n := rfl
def ndctl_f (n : Nat) : Nat := n * 3
theorem ndctl_c : ndctl_f 5 = 15 := by decide
theorem ndctl_d : ndctl_f 7 = 21 := rfl
