# Item 69

**Area:** Robertson at t = 1e11

**Source:** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `y₁ : ℝ → ℝ`, `y₂ : ℝ → ℝ`, `y₃ : ℝ → ℝ`:

**assuming**

1. the functions `y₁`, `y₂`, `y₃` (concentrations [A], [B], [C]) solve `y₁`′ = −`1 / 25`·`y₁` + `10000`·`y₂`·`y₃`, `y₂`′ = `1 / 25`·`y₁` − `10000`·`y₂`·`y₃` − `30000000`·`y₂`², `y₃`′ = `30000000`·`y₂`² (the rate equations of the network A → B, B + C → A + C, 2B → B + C) on the time interval [0, `100000000000`] (derivatives taken within [0, `100000000000`]), with initial values `y₁`(0) = `1`, `y₂`(0) = `0`, `y₃`(0) = `0`

**then**

1. `20833401494 / 1000000000000000000 < y₁ 100000000000`
2. `y₁ 100000000000 < 20833401500 / 1000000000000000000`
3. `83333 / 1000000000000000000 < y₂ 100000000000`
4. `y₂ 100000000000 < 83334 / 1000000000000000000`
5. `99999997916651 / 100000000000000 < y₃ 100000000000`
6. `y₃ 100000000000 < 99999997916652 / 100000000000000`

Program definitions in this claim:

- `IsRobSolution k₁ k₂ k₃ a₀ b₀ c₀ T y₁ y₂ y₃` — **PINNED** (pin theorem `robSpec_pins`): the functions `y₁`, `y₂`, `y₃` (concentrations [A], [B], [C]) solve `y₁`′ = −`k₁`·`y₁` + `k₂`·`y₂`·`y₃`, `y₂`′ = `k₁`·`y₁` − `k₂`·`y₂`·`y₃` − `k₃`·`y₂`², `y₃`′ = `k₃`·`y₂`² (the rate equations of the network A → B, B + C → A + C, 2B → B + C) on the time interval [0, `T`] (derivatives taken within [0, `T`]), with initial values `y₁`(0) = `a₀`, `y₂`(0) = `b₀`, `y₃`(0) = `c₀`

## Author's paraphrase (hand-written; checked only by prose rules)

Certified state of Robertson's stiff network at t = 10¹¹: for k₁ = 1/25, k₂ = 10⁴,
k₃ = 3·10⁷ and initial concentrations (1, 0, 0), every solution of the rate equations on
[0, 10¹¹] has 0.000000020833401494 < y₁(10¹¹) < 0.0000000208334015,
0.000000000000083333 < y₂(10¹¹) < 0.000000000000083334 and
0.99999997916651 < y₃(10¹¹) < 0.99999997916652.

## Formal statement (Lean 4)

```lean
theorem rob_state1e11 {y₁ y₂ y₃ : ℝ → ℝ}
    (h : Checked.Sim.Robertson.IsRobSolution (1 / 25) 10000 30000000 1 0 0 100000000000 y₁ y₂ y₃) :
    20833401494 / 1000000000000000000 < y₁ 100000000000 ∧
    y₁ 100000000000 < 20833401500 / 1000000000000000000 ∧
    83333 / 1000000000000000000 < y₂ 100000000000 ∧
    y₂ 100000000000 < 83334 / 1000000000000000000 ∧
    99999997916651 / 100000000000000 < y₃ 100000000000 ∧
    y₃ 100000000000 < 99999997916652 / 100000000000000 := …
```

## Definitions it uses

See GLOSSARY.md: `Sim.Robertson.IsRobSolution`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: IsRobSolution.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `rob_state1e11`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): IsRobSolution: k₁ = 1/25, k₂ = 10000, k₃ = 30000000, a₀ = 1, b₀ = 0, c₀ = 0, T = 100000000000.
- Source file: `Checked/Sim/RobLong.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 69
