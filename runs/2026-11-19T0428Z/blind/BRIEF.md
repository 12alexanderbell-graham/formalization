# Blind restatement brief (Lane–Emden, index four)

You have NOT seen any Lean statement of this claim. Write, from the informal claim below alone, a Lean 4 + Mathlib theorem statement (proof `sorry`) that says exactly what the claim says, under the most natural mathematical reading. Put a module doc listing every reading choice you made (what a solution is, regularity at the centre, where the equation is required, what "first zero" means, how the constants are defined). Use only Mathlib definitions. Namespace `Work.Math.LaneEmden4Blind`, theorem name `blind_laneEmden4`. Write the file to `runs/2026-11-19T0428Z/blind/LaneEmden4Blind.lean` (only that file). Do not read any other file of the repository.

**Claim.** Let θ be the solution of the Lane–Emden equation of index n = 4,

  θ'' + (2/ξ) θ' + θ⁴ = 0,  θ(0) = 1,  θ'(0) = 0 (regular at the centre),

considered on 0 ≤ ξ ≤ 16. Then θ has a first zero ξ₁ with 14.97154634 ≤ ξ₁ ≤ 14.97154636; the mass factor ω₄ = −ξ₁² θ'(ξ₁) satisfies 1.79722991 ≤ ω₄ ≤ 1.79722992; and the central concentration ρ_c/ρ̄ = ξ₁³/(3 ω₄) satisfies 622.407879 ≤ ρ_c/ρ̄ ≤ 622.407886. The claim is meant for every function satisfying the equation and the centre conditions (no uniqueness is assumed).
