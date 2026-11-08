# Item 56

**Area:** Rigorous simulation of a stiff network

**Source:** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `y₁ : ℝ → ℝ`, `y₂ : ℝ → ℝ`, `y₃ : ℝ → ℝ`:

**assuming**

1. the functions `y₁`, `y₂`, `y₃` (concentrations of A, B, C) solve the rate equations of the reaction network in which A turns into B with rate constant `k₁ := 1 / 25`, B and C turn into A and C with rate constant `k₂ := 10000`, and two B turn into B and C with rate constant `k₃ := 30000000`, on the time interval [0, `T := 40`] (derivatives taken within [0, `T := 40`]), with initial values `a₀ := 1`, `b₀ := 0`, `c₀ := 0` at time 0

**then**

1. `7158270 / 10000000 < y₁ 40`
2. `y₁ 40 < 7158271 / 10000000`
3. `91855 / 10000000000 < y₂ 40`
4. `y₂ 40 < 91856 / 10000000000`
5. `2841637 / 10000000 < y₃ 40`
6. `y₃ 40 < 2841638 / 10000000`

Program definitions in this claim:

- `IsRobSolution k₁ k₂ k₃ a₀ b₀ c₀ T y₁ y₂ y₃` — **PINNED** (pin theorem `robSpec_pins`): phrase (hand-written, linted): the functions `y₁`, `y₂`, `y₃` (concentrations of A, B, C) solve the rate equations of the reaction network in which A turns into B with rate constant `k₁`, B and C turn into A and C with rate constant `k₂`, and two B turn into B and C with rate constant `k₃`, on the time interval [0, `T`] (derivatives taken within [0, `T`]), with initial values `a₀`, `b₀`, `c₀` at time 0; by definition, means (`y₁ 0 = a₀`) and (`y₂ 0 = b₀`) and (`y₃ 0 = c₀`) and (for every `t : ℝ`, if `t ∈ Set.Icc 0 T`, then (`HasDerivWithinAt y₁ (-k₁ * y₁ t + k₂ * y₂ t * y₃ t) (Set.Icc 0 T) t`) and (`HasDerivWithinAt y₂ (k₁ * y₁ t - k₂ * y₂ t * y₃ t - k₃ * y₂ t ^ 2) (Set.Icc 0 T) t`) and (`HasDerivWithinAt y₃ (k₃ * y₂ t ^ 2) (Set.Icc 0 T) t`))

## Author's paraphrase (hand-written; checked only by prose rules)

Certified state of Robertson's stiff network at t = 40: for k₁ = 1/25, k₂ = 10⁴,
k₃ = 3·10⁷ and initial concentrations (1, 0, 0), every solution of the rate equations on
[0, 40] has 0.7158270 < y₁(40) < 0.7158271, 0.0000091855 < y₂(40) < 0.0000091856 and
0.2841637 < y₃(40) < 0.2841638.

## Formal statement (Lean 4)

```lean
theorem rob_state40 {y₁ y₂ y₃ : ℝ → ℝ}
    (h : IsRobSolution (1 / 25) 10000 30000000 1 0 0 40 y₁ y₂ y₃) :
    7158270 / 10000000 < y₁ 40 ∧ y₁ 40 < 7158271 / 10000000 ∧
    91855 / 10000000000 < y₂ 40 ∧ y₂ 40 < 91856 / 10000000000 ∧
    2841637 / 10000000 < y₃ 40 ∧ y₃ 40 < 2841638 / 10000000 := …
```

## Definitions it uses

See GLOSSARY.md: `Sim.Robertson.IsRobSolution`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: IsRobSolution.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `rob_state40`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): IsRobSolution: k₁ = 1/25, k₂ = 10000, k₃ = 30000000, a₀ = 1, b₀ = 0, c₀ = 0, T = 40.
- Source file: `Checked/Sim/Robertson.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 56
