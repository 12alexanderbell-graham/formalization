# Item 08

**Area:** Certified numbers of the findings

**Source:** Aviles, Gruber, Luongo, Quevedo, PRD 86, 123516 (2012), arXiv:1204.2007 (v1 and v2), Eq. (15): misprinted ΛCDM l₀ and m₀

## Claim in plain words (the system's own text)

The printed `l₀ = 1 + 3Ω − (27/2)Ω²` at `Ω = 0.3` is `0.685`.

## Formal statement (Lean 4)

```lean
theorem F1_printedL0 : RoundsTo (1 + 3 * (3 / 10) - 27 / 2 * (3 / 10) ^ 2) 0.685 3 := …
```

## Definitions it uses

See GLOSSARY.md: `Records.RoundsTo`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Source file: `Checked/Records/Findings.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 08
