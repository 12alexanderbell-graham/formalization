# Item 41

**Area:** Certified numbers of the findings

**Source:** Demianski, Piedipalumbo, Sawant, Amati, A&A 598, A113 (2017), arXiv:1609.09631 (v1, v2), p. 3: flat z-series D⁴_L has −105q₀⁴ (should be +105q₀⁴) and D⁴_A (Eq. (23)) has +137j₀ (should be −137j₀); the D⁴_L error is reprinted in Lusso et al., A&A 628, L4 (2019), arXiv:1907.07692 (v1–v4), the quasar+SN+GRB paper claiming > 4σ tension with flat ΛCDM

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**It holds that**

1. `RoundsTo (-210 * have q₀ := -4 / 5; q₀ ^ 4) (-86) 0`
2. `RoundsTo (7 / 4 * have q₀ := -4 / 5; q₀ ^ 4 * have z := 1; z ^ 4) 0.72 2`

Program definitions in this claim:

- `RoundsTo x d k` — MATH, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_RoundsTo`) (for `x : ℝ`, `d : ℝ`, `k : ℕ`): means `|x - d| ≤ 1 / (2 * 10 ^ k)`

## Author's paraphrase (hand-written; checked only by prose rules)

At `q₀ = −0.80`: the shift `l₀ ↦ l₀ − 210q₀⁴` that absorbs the D⁴_L error is `−86`, and the
error `(7/4)q₀⁴ z⁴` inside the bracket at `z = 1` is `0.72`.

## Formal statement (Lean 4)

```lean
theorem F11_sizes :
    RoundsTo (-210 * (let q₀ := …
```

## Definitions it uses

See GLOSSARY.md: `Records.RoundsTo`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): RoundsTo: d = -86, k = 0, d = 0.72, k = 2.
- Source file: `Checked/Records/Findings.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 41
