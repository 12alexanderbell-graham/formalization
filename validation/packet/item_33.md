# Item 33

**Area:** Rigorous simulation

**Source:** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**It holds that**

- there is `x : ℝ → ℝ` such that the position as function of time `x` is a Duffing oscillator initial value problem solution with the linear stiffness coefficient `k := 1`, the cubic stiffness coefficient `β := 1`, the initial position `x₀ := 1`, the initial velocity `v₀ := 0` and the final time of the interval `T := 6 / 5` (restoring force for positive stiffness, acceleration equals minus force terms; the second derivative plus `k := 1` times `x` plus `β := 1` times `x` cubed vanishes; `k := 1` is the linear stiffness and `β := 1` the cubic coefficient; `x₀ := 1` is the initial position and `v₀ := 0` the initial velocity; holds on the closed time interval from zero to `T := 6 / 5`; derivatives at the endpoints are one-sided)

Program definitions in this claim:

- `IsDuffingSolution k β x₀ v₀ T x` — **PINNED** (pin theorem `duffingSpec_pins`): phrase (hand-written, linted): the position as function of time `x` is a Duffing oscillator initial value problem solution with the linear stiffness coefficient `k`, the cubic stiffness coefficient `β`, the initial position `x₀`, the initial velocity `v₀` and the final time of the interval `T` (restoring force for positive stiffness, acceleration equals minus force terms; the second derivative plus `k` times `x` plus `β` times `x` cubed vanishes; `k` is the linear stiffness and `β` the cubic coefficient; `x₀` is the initial position and `v₀` the initial velocity; holds on the closed time interval from zero to `T`; derivatives at the endpoints are one-sided); by definition, means (`x 0 = x₀`) and (there is `v : ℝ → ℝ` such that (`v 0 = v₀`) and (for every `t : ℝ`, if `t ∈ Set.Icc 0 T`, then (`HasDerivWithinAt x (v t) (Set.Icc 0 T) t`) and (`HasDerivWithinAt v (-k * x t - β * x t ^ 3) (Set.Icc 0 T) t`))). Phrase lines proved in Lean (statements in PHRASE_LINES.md): «x₀ is the initial position and v₀ the initial velocity» only assuming `0 < T`; the position as function of time `x` is a Duffing oscillator initial value problem solution with the linear stiffness coefficient `k`, the cubic stiffness coefficient `β`, the initial position `x₀`, the initial velocity `v₀` and the final time of the interval `T` (restoring force for positive stiffness, acceleration equals minus force terms; the second derivative plus `k` times `x` plus `β` times `x` cubed vanishes; `k` is the linear stiffness and `β` the cubic coefficient; `x₀` is the initial position and `v₀` the initial velocity; holds on the closed time interval from zero to `T`; derivatives at the endpoints are one-sided)

## Author's paraphrase (hand-written; checked only by prose rules)

There is a solution of the Duffing initial value problem x'' + x + x³ = 0, x(0) = 1,
x'(0) = 0 on the time interval [0, 6/5] (derivatives within the interval).

## Formal statement (Lean 4)

```lean
theorem duffing_solution_exists : ∃ x : ℝ → ℝ, IsDuffingSolution 1 1 1 0 (6 / 5) x := …
```

## Definitions it uses

See GLOSSARY.md: `Sim.Duffing.IsDuffingSolution`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: IsDuffingSolution.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): IsDuffingSolution: k = 1, β = 1, x₀ = 1, v₀ = 0, T = 6/5.
- Source file: `Checked/Sim/Duffing.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 33
