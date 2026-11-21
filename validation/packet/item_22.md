# Item 22

**Area:** F4–F7

**Source (hand-written: the author's title of the finding or a fixed source line; no check reads it):** Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421, Sec. XI ("testing F(R) gravity by cosmography"), Eq. (11.31), from Capozziello, Cardone, Salzano 2008 (arXiv:0802.1583, PRD 78, 063504) Eq. (33): the common denominator R of the F(R₀), F″(R₀), F‴(R₀) formulas is wrong, so the printed F(R₀) formula (11.21) fails the paper's own ΛCDM check (11.40); also (11.13) d³R₀/dt³ has a sign error

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**Status (generated):** the statement is proved in module `Checked.Records.Findings` of `Checked`; axioms, computed by Lean when this page was generated: `Classical.choice`, `Quot.sound`, `propext`. This status is decided by Lean and the registry `scripts/trust/headlines.txt`, never by prose: a headline is withdrawn only by removing it from `Checked` and the registry, which removes it from this page. **Fidelity record (generated; what has been machine-checked about what the statement means, not a proof that it matches its source):** open fidelity objections on record (`scripts/trust/objections.txt`, where every objection to the meaning of a listed headline is entered when it is first written anywhere): none; non-vacuity: nothing to witness (the statement has no hypothesis to meet); hypotheses: none numbered; statement literals: no blind second reading registered; 8 literals of the statement are grandfathered as never read twice (`scripts/trust/literal_baseline.txt`); the statement is frozen (`scripts/trust/frozen.txt`): changing it needs a `LEDGER.md` entry naming it (`check_relock.py`), and a changed statement changes the claim on this page. CI regenerates this page on every push and fails if the committed copy differs, so it cannot lag the Lean sources.

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

## Your answers: use ANSWER_FORM.md, item 22
