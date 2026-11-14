# Item 38

**Area:** F4–F7

**Source:** Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421, Eqs. (10.38)–(10.51), verbatim from Capozziello & Salzano 2009 (arXiv:0902.0088) Eqs. (31)–(52): z-redshift d_L and d_A fourth-order coefficients D⁴_L, D⁴_A miss the curvature-squared term

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**It holds that**

1. `RoundsTo (have k := 1 / 100; have z := 2; k ^ 2 * z ^ 4 / 120) 13e-6 6`
2. `RoundsTo (100 * have z := 1; z ^ 5 / 120 / (z + z ^ 2 / 2)) 0.56 2`
3. `RoundsTo (100 * have z := 2; z ^ 5 / 120 / (z + z ^ 2 / 2)) 6.7 1`

Program definitions in this claim:

- `RoundsTo x d k` — MATH, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_RoundsTo`) (for `x : ℝ`, `d : ℝ`, `k : ℕ`): means `|x - d| ≤ 1 / (2 * 10 ^ k)`

## Author's paraphrase (hand-written; checked only by prose rules)

Size of the omitted `k²z⁴/120`: for `|k| = 0.01` at `z = 2` it is `1.3 × 10⁻⁵`. In Milne
(`H₀d_L = z + z²/2` exactly) the omitted `z⁵/120` relative to `H₀d_L` is `0.56 %` at `z = 1` and
`6.7 %` at `z = 2`.

## Formal statement (Lean 4)

```lean
theorem F8_sizes :
    RoundsTo (let k := …
```

## Definitions it uses

See GLOSSARY.md: `Records.RoundsTo`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): RoundsTo: d = 0.000013, k = 6, d = 0.56, k = 2, d = 6.7, k = 1.
- Source file: `Checked/Records/Findings.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 38
