# Item 31

**Area:** Certified numbers of the findings

**Source:** Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421, Sec. XI ("testing F(R) gravity by cosmography"), Eq. (11.31), from Capozziello, Cardone, Salzano 2008 (arXiv:0802.1583, PRD 78, 063504) Eq. (33): the common denominator R of the F(R₀), F″(R₀), F‴(R₀) formulas is wrong, so the printed F(R₀) formula (11.21) fails the paper's own ΛCDM check (11.40); also (11.13) d³R₀/dt³ has a sign error

## Claim in plain words (the system's own text)

At `Ω = 0.25` the printed (11.21) gives `F(R₀) = 0.277 H₀²`; the ΛCDM value `3H₀²(Ω − 2)` is
`−5.25 H₀²` (`H₀ = 1`).

## Formal statement (Lean 4)

```lean
theorem F9_values :
    RoundsTo (27 * (1 / 4) ^ 2 * ((1 / 4) - 2) * (27 * (1 / 4) ^ 2 + 60 * (1 / 4) + 112) /
      (243 * (1 / 4) ^ 4 + 540 * (1 / 4) ^ 3 - 6264 * (1 / 4) ^ 2 + 9360 * (1 / 4) - 3328)) 0.277 3 ∧
    RoundsTo (3 * ((1 / 4 : ℝ) - 2)) (-5.25) 2 := …
```

## Definitions it uses

See GLOSSARY.md: `Records.RoundsTo`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Source file: `Checked/Records/Findings.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 31
