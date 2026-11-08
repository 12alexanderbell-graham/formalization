# Item 37

**Area:** Rigorous simulation

**Source:** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `x : ℝ → ℝ`:

**assuming**

1. the function `x` solves the Duffing equation with stiffness `k := 1` and cubic coefficient `β := 1`, initial position `x₀ := 1` and initial velocity `v₀ := 0` on the time interval [0, `T := 6 / 5`] (derivatives taken within [0, `T := 6 / 5`])

**then**

1. for every `t : ℝ`, if `t ∈ Set.Icc 0 (1192005 / 1000000)`, then `0 < x t`
2. `x (1192006 / 1000000) < 0`

Program definitions in this claim:

- `IsDuffingSolution k β x₀ v₀ T x` — **PINNED** (pin theorem `duffingSpec_pins`): phrase (hand-written, linted): the function `x` solves the Duffing equation with stiffness `k` and cubic coefficient `β`, initial position `x₀` and initial velocity `v₀` on the time interval [0, `T`] (derivatives taken within [0, `T`]); by definition, means (`x 0 = x₀`) and (there is `v : ℝ → ℝ` such that (`v 0 = v₀`) and (for every `t : ℝ`, if `t ∈ Set.Icc 0 T`, then (`HasDerivWithinAt x (v t) (Set.Icc 0 T) t`) and (`HasDerivWithinAt v (-k * x t - β * x t ^ 3) (Set.Icc 0 T) t`)))

## Author's paraphrase (hand-written; checked only by prose rules)

Certified first zero of the Duffing oscillator x'' + x + x³ = 0 released from rest at
x = 1: every solution on the time interval [0, 6/5] (derivatives within the interval) is strictly
positive at all times in [0, 1.192005] and strictly negative at time 1.192006, so its earliest
zero lies strictly between 1.192005 and 1.192006. Proved by a validated enclosure of every
solution (rational Taylor cells, exact defect bounds, energy box, Grönwall).

## Formal statement (Lean 4)

```lean
theorem duffing_first_zero_sol (x : ℝ → ℝ) (hx : IsDuffingSolution 1 1 1 0 (6 / 5) x) :
    (∀ t ∈ Icc (0 : ℝ) (1192005 / 1000000), 0 < x t) ∧ x (1192006 / 1000000) < 0 := …
```

## Definitions it uses

See GLOSSARY.md: `Sim.Duffing.IsDuffingSolution`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: IsDuffingSolution.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `duffing_first_zero_sol`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): IsDuffingSolution: k = 1, β = 1, x₀ = 1, v₀ = 0, T = 6/5.
- Source file: `Checked/Sim/Duffing.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 37
