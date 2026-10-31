# Item 19

**Area:** Certified numbers of the findings

**Source:** Demianski, Piedipalumbo, Sawant, Amati, A&A 598, A113 (2017), arXiv:1609.09631 (v1, v2), p. 3: flat z-series D⁴_L has −105q₀⁴ (should be +105q₀⁴) and D⁴_A (Eq. (23)) has +137j₀ (should be −137j₀); the D⁴_L error is reprinted in Lusso et al., A&A 628, L4 (2019), arXiv:1907.07692 (v1–v4), the quasar+SN+GRB paper claiming > 4σ tension with flat ΛCDM

## Claim in plain words (the system's own text)

At `q₀ = −0.80`: the shift `l₀ ↦ l₀ − 210q₀⁴` that absorbs the D⁴_L error is `−86`, and the
error `(7/4)q₀⁴ z⁴` inside the bracket at `z = 1` is `0.72`.

## Formal statement (Lean 4)

```lean
theorem F11_sizes :
    RoundsTo (-210 * (-4 / 5) ^ 4) (-86) 0 ∧ RoundsTo (7 / 4 * (-4 / 5) ^ 4 * 1 ^ 4) 0.72 2 := …
```

## Definitions it uses

See GLOSSARY.md: `Records.RoundsTo`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Source file: `Checked/Records/Findings.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 19
