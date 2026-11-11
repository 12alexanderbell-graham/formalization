# Item 53

**Area:** Data claims

**Source:** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `N : ℝ`, `c : ℝ`:

**assuming**

1. `5 < N`
2. `N ≤ 31`
3. `|c + 2 * 4 + 2 * 4 * (4 + 1) / (N - 4 - 1) - 23.99| ≤ 5e-3`

**then**

- `5e-3 < |c + 4 * Real.log N - 28.72|`

## Author's paraphrase (hand-written; checked only by prose rules)

Table 5, piecewise-linear row (k = 4): for every N with 5 < N ≤ 31 and every value c of
−2 ln L_max, if c + 8 + 40/(N − 5) is within 0.005 of the printed AICc 23.99, then
c + 4 ln N differs from the printed BIC 28.72 by more than 0.005.

## Formal statement (Lean 4)

```lean
theorem table5_pw_inconsistent (N c : ℝ) (hN : 5 < N) (hN31 : N ≤ 31)
    (hA : |c + 2 * 4 + 2 * 4 * (4 + 1) / (N - 4 - 1) - 23.99| ≤ 0.005) :
    0.005 < |c + 4 * Real.log N - 28.72| := …
```

## Definitions it uses

Only Mathlib notions.

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `table5_pw_inconsistent`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Data/Moresco16.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 53
