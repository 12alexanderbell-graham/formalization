# Item 37

**Area:** Rigorous simulation of a stiff network

**Source:** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**It holds that**

- there is `y₁ : ℝ → ℝ` such that there is `y₂ : ℝ → ℝ` such that there is `y₃ : ℝ → ℝ` such that the concentration of species A over time `y₁`, the concentration of species B over time `y₂` and the concentration of species C over time `y₃` are a Robertson chemical kinetics initial value problem solution: they solve the rate equations of the reaction network in which A turns into B with rate constant of the first reaction `k₁ := 1 / 25`, B and C turn into A and C with rate constant of the second reaction `k₂ := 10000`, and two B turn into B and C with rate constant of the third reaction `k₃ := 30000000`, on the time interval from 0 to the final time of the interval `T := 40` (derivatives taken within [0, `T := 40`]), with initial concentration of species A `a₀ := 1`, initial concentration of species B `b₀ := 0` and initial concentration of species C `c₀ := 0` at time 0

Program definitions in this claim:

- `IsRobSolution k₁ k₂ k₃ a₀ b₀ c₀ T y₁ y₂ y₃` — **PINNED** (pin theorem `robSpec_pins`): phrase (hand-written, linted): the concentration of species A over time `y₁`, the concentration of species B over time `y₂` and the concentration of species C over time `y₃` are a Robertson chemical kinetics initial value problem solution: they solve the rate equations of the reaction network in which A turns into B with rate constant of the first reaction `k₁`, B and C turn into A and C with rate constant of the second reaction `k₂`, and two B turn into B and C with rate constant of the third reaction `k₃`, on the time interval from 0 to the final time of the interval `T` (derivatives taken within [0, `T`]), with initial concentration of species A `a₀`, initial concentration of species B `b₀` and initial concentration of species C `c₀` at time 0; by definition, means (`y₁ 0 = a₀`) and (`y₂ 0 = b₀`) and (`y₃ 0 = c₀`) and (for every `t : ℝ`, if `t ∈ Set.Icc 0 T`, then (`HasDerivWithinAt y₁ (-k₁ * y₁ t + k₂ * y₂ t * y₃ t) (Set.Icc 0 T) t`) and (`HasDerivWithinAt y₂ (k₁ * y₁ t - k₂ * y₂ t * y₃ t - k₃ * y₂ t ^ 2) (Set.Icc 0 T) t`) and (`HasDerivWithinAt y₃ (k₃ * y₂ t ^ 2) (Set.Icc 0 T) t`))

## Author's paraphrase (hand-written; checked only by prose rules)

There is a solution of the rate equations of Robertson's network on [0, 40] with k₁ = 1/25,
k₂ = 10⁴, k₃ = 3·10⁷ and initial concentrations (1, 0, 0).

## Formal statement (Lean 4)

```lean
theorem rob_exists : ∃ y₁ y₂ y₃ : ℝ → ℝ,
    IsRobSolution (1 / 25) 10000 30000000 1 0 0 40 y₁ y₂ y₃ := …
```

## Definitions it uses

See GLOSSARY.md: `Sim.Robertson.IsRobSolution`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: IsRobSolution.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): IsRobSolution: k₁ = 1/25, k₂ = 10000, k₃ = 30000000, a₀ = 1, b₀ = 0, c₀ = 0, T = 40.
- Source file: `Checked/Sim/Robertson.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 37
