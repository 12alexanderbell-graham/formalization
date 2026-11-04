# Item 47

**Area:** Rigorous simulation

**Source:** see the claim

## Claim in plain words (the system's own text)

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
- Source file: `Checked/Sim/Duffing.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 47
