# Blind restatement brief (Lane–Emden, index five halves)

You have NOT seen any Lean statement of this claim. Write, from the informal claim below alone, a Lean 4 + Mathlib theorem statement (proof `sorry`) that says exactly what the claim says, under the most natural mathematical reading. Put a module doc listing every reading choice you made (what a solution is, regularity at the centre, where the equation is required, how the power θ^(5/2) is written and what it means where θ < 0, what "first zero" means, how the constants are defined). Use only Mathlib definitions. Namespace `Work.Math.LaneEmden52Blind`, theorem name `blind_laneEmden52`. Write the file to `runs/2026-11-19T1628Z/blind/LaneEmden52Blind.lean` (only that file). Do not read any other file of the repository. Check that it compiles with `export PATH=$HOME/.elan/bin:$PATH; cd /home/claude/formalization; lake env lean runs/2026-11-19T1628Z/blind/LaneEmden52Blind.lean` (timeout 600000 ms; `import Mathlib` is fine). Do not run `lake build`.

**Claim.** Let θ be the solution of the Lane–Emden equation of index n = 5/2,

  θ'' + (2/ξ) θ' + θ^(5/2) = 0,  θ(0) = 1,  θ'(0) = 0 (regular at the centre),

considered on 0 ≤ ξ ≤ 6. Then θ has a first zero ξ₁ with 5.35527545 ≤ ξ₁ ≤ 5.35527546; the mass factor ω = −ξ₁² θ'(ξ₁) satisfies 2.18719956 ≤ ω ≤ 2.18719957; and the central concentration ρ_c/ρ̄ = ξ₁³/(3 ω) satisfies 23.40646222 ≤ ρ_c/ρ̄ ≤ 23.40646231. The claim is meant for every function satisfying the equation and the centre conditions (no uniqueness is assumed).
