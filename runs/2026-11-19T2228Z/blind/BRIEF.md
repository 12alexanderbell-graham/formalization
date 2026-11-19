# Blind restatement brief (Lane–Emden, index seven halves)

You have NOT seen any Lean statement of this claim. Write, from the informal claim below alone, a Lean 4 + Mathlib theorem statement (proof `sorry`) that says exactly what the claim says, under the most natural mathematical reading. Put a module doc listing every reading choice you made (what a solution is, regularity at the centre, where the equation is required, how the power θ^(7/2) is written and what it means where θ < 0, what "first zero" means, how the constants are defined). Use only Mathlib definitions. Namespace `Work.Math.LaneEmden72Blind`, theorem name `blind_laneEmden72`. Write the file to `runs/2026-11-19T2228Z/blind/LaneEmden72Blind.lean` (only that file). Do not read any other file of the repository. Check that it compiles with `export PATH=$HOME/.elan/bin:$PATH; cd /home/claude/formalization; lake env lean runs/2026-11-19T2228Z/blind/LaneEmden72Blind.lean` (timeout 600000 ms; `import Mathlib` is fine). Do not run `lake build`.

**Claim.** Let θ be the solution of the Lane–Emden equation of index n = 7/2,

  θ'' + (2/ξ) θ' + θ^(7/2) = 0,  θ(0) = 1,  θ'(0) = 0 (regular at the centre),

considered on 0 ≤ ξ ≤ 10. Then θ has a first zero ξ₁ with 9.53580534 ≤ ξ₁ ≤ 9.53580535; the mass factor ω = −ξ₁² θ'(ξ₁) satisfies 1.89055709 ≤ ω ≤ 1.89055710; and the central concentration ρ_c/ρ̄ = ξ₁³/(3 ω) satisfies 152.8836627 ≤ ρ_c/ρ̄ ≤ 152.8836632. The claim is meant for every function satisfying the equation and the centre conditions (no uniqueness is assumed).
