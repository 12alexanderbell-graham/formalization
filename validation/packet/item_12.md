# Item 12

**Area:** Fluid mechanics

**Source (hand-written: the author's title of the finding or a fixed source line; no check reads it):** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**Status (generated):** **The source's own form, as a blind reader wrote it from the source without seeing this statement (each body occurs in the statement below, `check_literals.py`):** `Checked.Trust.SecondReading.fskWedgeRhs` := `fun f p q η => -(f η * q η) - 1 / 2 * (1 - p η ^ 2)`; `Checked.Trust.SecondReading.fskHalfLineTyped` := `Set.Ici 0`; `Checked.Trust.SecondReading.fskHalfLine` := `Set.Ici 0`; `Checked.Trust.SecondReading.fskWall` := `fun g => g 0 = 0`; `Checked.Trust.SecondReading.fskEdge` := `nhds 1`; `Checked.Trust.SecondReading.fskWedgeShear` := `fun q => 0.927680039 < q 0 ∧ q 0 < 0.927680040`. the statement is proved in module `Checked.FalknerSkan.FalknerSkan` of `Checked`; axioms, computed by Lean when this page was generated: `Classical.choice`, `Quot.sound`, `propext`. This status is decided by Lean and the registry `scripts/trust/headlines.txt`, never by prose: a headline is withdrawn only by removing it from `Checked` and the registry, which removes it from this page. **Fidelity record (generated; what has been machine-checked about what the statement means, not a proof that it matches its source):** open fidelity objections on record (`scripts/trust/objections.txt`, where every objection to the meaning of a listed headline is entered when it is first written anywhere): none; non-vacuity: nothing to witness (the statement has no hypothesis to meet); hypotheses: none numbered; statement literals: 6 definitions written by a blind second reader of the source are registered for this statement in `scripts/trust/literal_readings.txt` and occur in it (`check_literals.py`) (printed at the head of this line); no literal of the statement is grandfathered as unread (`check_literals.py` requires every other literal to be read twice or certified by the proof); the statement is frozen (`scripts/trust/frozen.txt`): changing it needs a `LEDGER.md` entry naming it (`check_relock.py`), and a changed statement changes the claim on this page. CI regenerates this page on every push and fails if the committed copy differs, so it cannot lag the Lean sources.

**It holds that**

- there is `f : ℝ → ℝ` such that there is `p : ℝ → ℝ` such that there is `q : ℝ → ℝ` such that (for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt f (p η) (Set.Ici 0) η`) and (for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt p (q η) (Set.Ici 0) η`) and (for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt q (-(f η * q η) - 1 / 2 * (1 - p η ^ 2)) (Set.Ici 0) η`) and (`f 0 = 0`) and (`p 0 = 0`) and (`Filter.Tendsto p Filter.atTop (nhds 1)`) and (`0.927680039 < q 0`) and (`q 0 < 0.927680040`)

## Author's paraphrase (hand-written; checked only by prose rules)

Falkner–Skan β = 1/2, existence: there is a solution f of f''' + f f'' + (1 − f'²)/2 = 0 on
[0, ∞) (f has derivative p, p has derivative q, q has derivative −f q − (1 − p²)/2, one-sided
at 0) with f(0) = 0, p(0) = 0 and p(η) → 1 as η → ∞ whose wall value q(0) = f''(0) lies
strictly between 0.927680039 and 0.927680040.

## Formal statement (Lean 4)

```lean
theorem fs_half_exists : ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 / 2 * (1 - p η ^ 2)) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
    0.927680039 < q 0 ∧ q 0 < 0.927680040 := …
```

## Definitions it uses

Only Mathlib notions.

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/FalknerSkan/FalknerSkan.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 12
