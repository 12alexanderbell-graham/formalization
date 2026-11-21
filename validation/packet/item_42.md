# Item 42

**Area:** Mathematics/physics

**Source (hand-written: the author's title of the finding or a fixed source line; no check reads it):** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**Status (generated):** **The source's own form, as a blind reader wrote it from the source without seeing this statement (each body occurs in the statement below, `check_literals.py`):** `Checked.Trust.SecondReading.tfRhs` := `fun y x => y x ^ (3 / 2) / √x`; `Checked.Trust.SecondReading.tfDomain` := `Set.Ici 0`; `Checked.Trust.SecondReading.tfNucleus` := `fun y => y 0 = 1`; `Checked.Trust.SecondReading.tfInfinity` := `nhds 0`; `Checked.Trust.SecondReading.tfRegular` := `fun φ => ContinuousWithinAt φ (Set.Ici 0) 0`. the statement is proved in module `Checked.Math.ThomasFermiExists` of `Checked`; axioms, computed by Lean when this page was generated: `Classical.choice`, `Quot.sound`, `propext`. This status is decided by Lean and the registry `scripts/trust/headlines.txt`, never by prose: a headline is withdrawn only by removing it from `Checked` and the registry, which removes it from this page. **Fidelity record (generated; what has been machine-checked about what the statement means, not a proof that it matches its source):** open fidelity objections on record (`scripts/trust/objections.txt`, where every objection to the meaning of a listed headline is entered when it is first written anywhere): none; non-vacuity: nothing to witness (the statement has no hypothesis to meet); hypotheses: none numbered; statement literals: 5 definitions written by a blind second reader of the source are registered for this statement in `scripts/trust/literal_readings.txt` and occur in it (`check_literals.py`) (printed at the head of this line); no literal of the statement is grandfathered as unread (`check_literals.py` requires every other literal to be read twice or certified by the proof); the statement is frozen (`scripts/trust/frozen.txt`): changing it needs a `LEDGER.md` entry naming it (`check_relock.py`), and a changed statement changes the claim on this page. CI regenerates this page on every push and fails if the committed copy differs, so it cannot lag the Lean sources.

**It holds that**

- there is `y : ℝ → ℝ` such that there is `φ : ℝ → ℝ` such that (for every `x : ℝ`, if `0 ≤ x`, then `HasDerivWithinAt y (φ x) (Set.Ici 0) x`) and (for every `x : ℝ`, if `0 < x`, then `HasDerivAt φ (y x ^ (3 / 2) / √x) x`) and (`ContinuousWithinAt φ (Set.Ici 0) 0`) and (`y 0 = 1`) and (for every `x : ℝ`, if `0 ≤ x`, then `0 < y x`) and (`Filter.Tendsto y Filter.atTop (nhds 0)`)

## Author's paraphrase (hand-written; checked only by prose rules)

There is a solution y of the Thomas–Fermi equation y'' = y^{3/2}/√x on (0, ∞) with y' = φ on
[0, ∞), φ continuous at 0 from the right, y(0) = 1, y > 0 on [0, ∞) and y(x) → 0 as x → ∞.

## Formal statement (Lean 4)

```lean
theorem tf_exists : ∃ y φ : ℝ → ℝ,
    (∀ x, 0 ≤ x → HasDerivWithinAt y (φ x) (Ici 0) x) ∧
    (∀ x, 0 < x → HasDerivAt φ (y x ^ ((3 : ℝ) / 2) / Real.sqrt x) x) ∧
    ContinuousWithinAt φ (Ici 0) 0 ∧ y 0 = 1 ∧ (∀ x, 0 ≤ x → 0 < y x) ∧
    Tendsto y atTop (𝓝 0) := …
```

## Definitions it uses

Only Mathlib notions.

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Math/ThomasFermiExists.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 42
