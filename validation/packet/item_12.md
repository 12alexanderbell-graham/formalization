# Item 12

**Area:** Fluid mechanics

**Source:** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `S : ℝ`, `f : ℝ → ℝ`, `p : ℝ → ℝ`, `q : ℝ → ℝ`:

**assuming**

1. `15 / 2 ≤ S`
2. for every `η : ℝ`, if `η ∈ Set.Icc 0 S`, then `HasDerivWithinAt f (p η) (Set.Icc 0 S) η`
3. for every `η : ℝ`, if `η ∈ Set.Icc 0 S`, then `HasDerivWithinAt p (q η) (Set.Icc 0 S) η`
4. for every `η : ℝ`, if `η ∈ Set.Icc 0 S`, then `HasDerivWithinAt q (-(f η * q η) - 1 + p η ^ 2) (Set.Icc 0 S) η`
5. `f 0 = 0`
6. `p 0 = 0`
7. `q 0 = 1.2325876569`

**then**

- there is `η : ℝ` such that (`η ∈ Set.Ioc 0 (15 / 2)`) and (`1 < p η`) and (for every `s : ℝ`, if `s ∈ Set.Icc 0 η`, then `0 < q s`)

## Author's paraphrase (hand-written; checked only by prose rules)

Hiemenz stagnation-point flow, overshoot: for every S ≥ 15/2 and every solution of
f''' + f f'' + 1 − f'² = 0 on [0, S] (f has derivative p, p has derivative q, q has derivative
−f q − 1 + p², within [0, S]) with f(0) = 0, p(0) = 0 and q(0) = 1.2325876569, there is
η in (0, 15/2] with p(η) > 1 and q > 0 on [0, η].

## Formal statement (Lean 4)

```lean
theorem hiemenz_over (S : ℝ) (hS : 15 / 2 ≤ S) (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Icc (0 : ℝ) S, HasDerivWithinAt f (p η) (Icc 0 S) η)
    (hp : ∀ η ∈ Icc (0 : ℝ) S, HasDerivWithinAt p (q η) (Icc 0 S) η)
    (hq : ∀ η ∈ Icc (0 : ℝ) S, HasDerivWithinAt q (-(f η * q η) - 1 + p η ^ 2) (Icc 0 S) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hq0 : q 0 = 1.2325876569) :
    ∃ η ∈ Ioc (0 : ℝ) (15 / 2), 1 < p η ∧ ∀ s ∈ Icc 0 η, 0 < q s := …
```

## Definitions it uses

Only Mathlib notions.

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `hiemenz_over`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Hiemenz/Hiemenz.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 12
