# Item 20

**Area:** Certified numbers of the findings

**Source:** Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421, Sec. XI, Eqs. (11.42)–(11.45) (p. 121), from Capozziello, Cardone, Salzano 2008 (arXiv:0802.1583) Eqs. (43)–(44) and the display after (44): the first-order deviations η₂₀ = F″(R₀)H₀⁴/F(R₀), η₃₀ = F‴(R₀)H₀⁶/F(R₀) of F(R) from GR are wrong, formulas and numbers

## Claim in plain words (the system's own text)

The two factors of the hypothesis `(54Ω² − 29Ω − 2)(27Ω² + 24Ω − 32) ≠ 0` of `printedEta20_false_at`,
`printedEta30_false_at` vanish at `Ω ≈ 0.599` and `Ω ≈ 0.731` respectively (proved: a root of each,
rounded to three decimals). In words, not proved here: these are their only roots in `(0, 1)`, and
together with the root `Ω ≈ 0.176` of the printed denominator, where (11.42)–(11.43) are undefined
(`F10_printed_pole`), they are the points of `(0, 1)` the two refutations do not cover.

## Formal statement (Lean 4)

```lean
theorem F10_exceptions :
    (∃ r : ℝ, RoundsTo r 0.599 3 ∧ 54 * r ^ 2 - 29 * r - 2 = 0) ∧
    (∃ r : ℝ, RoundsTo r 0.731 3 ∧ 27 * r ^ 2 + 24 * r - 32 = 0) := …
```

## Definitions it uses

See GLOSSARY.md: `Records.RoundsTo`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Source file: `Checked/Records/Findings.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 20
