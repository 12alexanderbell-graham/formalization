# Item 20

**Area:** Data claims

**Source:** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `N : ℝ`, `c : ℝ`:

**assuming**

1. `4 < N`
2. `N ≤ 31`
3. `|c + 2 * 3 + 2 * 3 * (3 + 1) / (N - 3 - 1) - 21.41| ≤ 5e-3`

**then**

- `5e-3 < |c + 3 * Real.log N - 25.71|`

## Author's paraphrase (hand-written; checked only by prose rules)

Table 5, row oLCDM (k = 3): for every N with 4 < N ≤ 31 and every value c of −2 ln L_max,
if c + 6 + 24/(N − 4) is within 0.005 of the printed AICc 21.41, then c + 3 ln N differs from
the printed BIC 25.71 by more than 0.005.

## Formal statement (Lean 4)

```lean
theorem table5_oL_inconsistent (N c : ℝ) (hN : 4 < N) (hN31 : N ≤ 31)
    (hA : |c + 2 * 3 + 2 * 3 * (3 + 1) / (N - 3 - 1) - 21.41| ≤ 0.005) :
    0.005 < |c + 3 * Real.log N - 25.71| := …
```

## Definitions it uses

Only Mathlib notions.

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `table5_oL_inconsistent`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Data/Moresco16.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 20
