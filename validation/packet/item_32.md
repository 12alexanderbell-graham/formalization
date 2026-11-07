# Item 32

**Area:** Certified numbers of the findings

**Source:** Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421, Sec. XI ("testing F(R) gravity by cosmography"), Eq. (11.31), from Capozziello, Cardone, Salzano 2008 (arXiv:0802.1583, PRD 78, 063504) Eq. (33): the common denominator R of the F(R₀), F″(R₀), F‴(R₀) formulas is wrong, so the printed F(R₀) formula (11.21) fails the paper's own ΛCDM check (11.40); also (11.13) d³R₀/dt³ has a sign error

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**It holds that**

- there is `r : ℝ` such that (`RoundsTo r 0.538 3`) and (`243 * r ^ 4 + 540 * r ^ 3 - 6264 * r ^ 2 + 9360 * r - 3328 = 0`)

Program definitions in this claim:

- `RoundsTo x d k` — MATH, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_RoundsTo`) (for `x : ℝ`, `d : ℝ`, `k : ℕ`): means `|x - d| ≤ 1 / (2 * 10 ^ k)`

## Author's paraphrase (hand-written; checked only by prose rules)

The denominator of the printed (11.21) in ΛCDM vanishes at some `Ω ≈ 0.538`.

## Formal statement (Lean 4)

```lean
theorem F9_pole : ∃ r : ℝ, RoundsTo r 0.538 3 ∧
    243 * r ^ 4 + 540 * r ^ 3 - 6264 * r ^ 2 + 9360 * r - 3328 = 0 := …
```

## Definitions it uses

See GLOSSARY.md: `Records.RoundsTo`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): RoundsTo: d = 0.538, k = 3.
- Source file: `Checked/Records/Findings.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 32
