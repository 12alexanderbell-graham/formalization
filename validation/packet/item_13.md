# Item 13

**Area:** Rigorous simulation of a reaction network

**Source:** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**It holds that**

- there is `s : ℝ → ℝ` such that there is `e : ℝ → ℝ` such that there is `c : ℝ → ℝ` such that there is `p : ℝ → ℝ` such that the substrate concentration over time `s`, the free enzyme concentration over time `e`, the complex concentration over time `c` and the product concentration over time `p` are a Michaelis Menten mass action initial value problem solution with the binding rate constant `k₁ := 1`, the unbinding rate constant `km₁ := 1`, the catalytic rate constant `k₂ := 1`, the initial substrate concentration `s₀ := 1`, the initial free enzyme concentration `e₀ := 1`, the initial complex concentration `c₀ := 0`, the initial product concentration `p₀ := 0` and the final time of the interval `T := 13 / 5` (binding consumes substrate and free enzyme, forms complex; mass action kinetics of E plus S reversibly forming complex C; `k₁ := 1` is the rate constant of E plus S forming C; `km₁ := 1` is the rate constant of C returning to E plus S; `k₂ := 1` is the rate constant of C forming E plus P; `s` `e` `c` `p` are concentrations of S E C and P; holds on the closed time interval from zero to `T := 13 / 5`)

Program definitions in this claim:

- `IsMMSolution k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p` — **PINNED** (pin theorem `mmSpec_pins`): phrase (hand-written, linted): the substrate concentration over time `s`, the free enzyme concentration over time `e`, the complex concentration over time `c` and the product concentration over time `p` are a Michaelis Menten mass action initial value problem solution with the binding rate constant `k₁`, the unbinding rate constant `km₁`, the catalytic rate constant `k₂`, the initial substrate concentration `s₀`, the initial free enzyme concentration `e₀`, the initial complex concentration `c₀`, the initial product concentration `p₀` and the final time of the interval `T` (binding consumes substrate and free enzyme, forms complex; mass action kinetics of E plus S reversibly forming complex C; `k₁` is the rate constant of E plus S forming C; `km₁` is the rate constant of C returning to E plus S; `k₂` is the rate constant of C forming E plus P; `s` `e` `c` `p` are concentrations of S E C and P; holds on the closed time interval from zero to `T`); by definition, means (`s 0 = s₀`) and (`e 0 = e₀`) and (`c 0 = c₀`) and (`p 0 = p₀`) and (for every `t : ℝ`, if `t ∈ Set.Icc 0 T`, then (`HasDerivWithinAt s (-k₁ * e t * s t + km₁ * c t) (Set.Icc 0 T) t`) and (`HasDerivWithinAt e (-k₁ * e t * s t + (km₁ + k₂) * c t) (Set.Icc 0 T) t`) and (`HasDerivWithinAt c (k₁ * e t * s t - (km₁ + k₂) * c t) (Set.Icc 0 T) t`) and (`HasDerivWithinAt p (k₂ * c t) (Set.Icc 0 T) t`))

## Author's paraphrase (hand-written; checked only by prose rules)

There is a solution of the mass-action rate equations of the Michaelis–Menten mechanism
with k₁ = k₋₁ = k₂ = 1, [S]₀ = [E]₀ = 1, [C]₀ = [P]₀ = 0 on the time interval [0, 13/5]
(derivatives within the interval).

## Formal statement (Lean 4)

```lean
theorem mm_solution_exists :
    ∃ s e c p : ℝ → ℝ, IsMMSolution 1 1 1 1 1 0 0 (13 / 5) s e c p := …
```

## Definitions it uses

See GLOSSARY.md: `Sim.MichaelisMenten.IsMMSolution`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: IsMMSolution.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): IsMMSolution: k₁ = 1, km₁ = 1, k₂ = 1, s₀ = 1, e₀ = 1, c₀ = 0, p₀ = 0, T = 13/5.
- Source file: `Checked/Sim/MichaelisMenten.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 13
