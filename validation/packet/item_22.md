# Item 22

**Area:** Falkner–Skan reversed-flow rows β = −0.17, −0.18, −0.19

**Source (hand-written: the author's title of the finding or a fixed source line; no check reads it):** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**Status (generated):** **The source's own form, as a blind reader wrote it from the source without seeing this statement (each body occurs in the statement below, `check_literals.py`):** `Checked.Trust.SecondReading.fsAttLastRhs` := `fun f p q η => -(f η * q η) - -19 / 100 * (1 - p η ^ 2)`; `Checked.Trust.SecondReading.fskHalfLineTyped` := `Set.Ici 0`; `Checked.Trust.SecondReading.fskHalfLine` := `Set.Ici 0`; `Checked.Trust.SecondReading.fskWall` := `fun g => g 0 = 0`; `Checked.Trust.SecondReading.fskEdge` := `nhds 1`; `Checked.Trust.SecondReading.fsnDefectBelow` := `fun M p q η => M * (1 - p η) ≤ q η`; `Checked.Trust.SecondReading.stagSpeedBounded` := `fun p η => -1 ≤ p η ∧ p η ≤ 1`; `Checked.Trust.SecondReading.fsnWallValue` := `fun q => q 0`. the statement is proved in module `Checked.FalknerSkan.NegReversedRows` of `Checked`; axioms, computed by Lean when this page was generated: `Classical.choice`, `Quot.sound`, `propext`. This status is decided by Lean and the registry `scripts/trust/headlines.txt`, never by prose: a headline is withdrawn only by removing it from `Checked` and the registry, which removes it from this page. **Fidelity record (generated; what has been machine-checked about what the statement means, not a proof that it matches its source):** open fidelity objections on record (`scripts/trust/objections.txt`, where every objection to the meaning of a listed headline is entered when it is first written anywhere): none; non-vacuity: nothing to witness (the statement has no hypothesis to meet); hypotheses: none numbered; statement literals: 8 definitions written by a blind second reader of the source are registered for this statement in `scripts/trust/literal_readings.txt` and occur in it (`check_literals.py`) (printed at the head of this line); no literal of the statement is grandfathered as unread (`check_literals.py` requires every other literal to be read twice or certified by the proof); the statement is frozen (`scripts/trust/frozen.txt`): changing it needs a `LEDGER.md` entry naming it (`check_relock.py`), and a changed statement changes the claim on this page. CI regenerates this page on every push and fails if the committed copy differs, so it cannot lag the Lean sources.

**It holds that**

- there is `f : ℝ → ℝ` such that there is `p : ℝ → ℝ` such that there is `q : ℝ → ℝ` such that (for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt f (p η) (Set.Ici 0) η`) and (for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt p (q η) (Set.Ici 0) η`) and (for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt q (-(f η * q η) - -19 / 100 * (1 - p η ^ 2)) (Set.Ici 0) η`) and (`f 0 = 0`) and (`p 0 = 0`) and (`Filter.Tendsto p Filter.atTop (nhds 1)`) and (for every `η : ℝ`, if `η ∈ Set.Ici 0`, then (`-1 ≤ p η`) and (`p η ≤ 1`)) and (for every `M : ℝ`, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`) and (`-713359061e-10 < q 0`) and (`q 0 < -713359060e-10`)

## Author's paraphrase (hand-written; checked only by prose rules)

Falkner–Skan with β = −19/100: there is a solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0 on [0, ∞) with
f(0) = 0, p(0) = 0, p → 1, −1 ≤ p ≤ 1 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`, with
−0.0713359061 < q(0) < −0.0713359060.

## Formal statement (Lean 4)

```lean
theorem fs_neg_reversed_wall_shear_19_exists :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-19 / 100) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧
      -0.0713359061 < q 0 ∧ q 0 < -0.0713359060 := …
```

## Definitions it uses

Only Mathlib notions.

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/FalknerSkan/NegReversedRows.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 22
