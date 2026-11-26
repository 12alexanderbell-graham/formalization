# Item 40

**Area:** Fluid mechanics

**Source (hand-written: the author's title of the finding or a fixed source line; no check reads it):** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**Status (generated):** **The source's own form, as a blind reader wrote it from the source without seeing this statement (each body occurs in the statement below, `check_literals.py`):** `Checked.Trust.SecondReading.homannRhs` := `fun f p q η => -(2 * f η * q η) - 1 + p η ^ 2`; `Checked.Trust.SecondReading.homannHalfLineTyped` := `Set.Ici 0`; `Checked.Trust.SecondReading.homannHalfLine` := `Set.Ici 0`; `Checked.Trust.SecondReading.homannWall` := `fun g => g 0 = 0`; `Checked.Trust.SecondReading.homannEdge` := `nhds 1`; `Checked.Trust.SecondReading.homannShear` := `fun q => 1.3119376938 < q 0 ∧ q 0 < 1.3119376939`. the statement is proved in module `Checked.Homann.Homann` of `Checked`; axioms, computed by Lean when this page was generated: `Classical.choice`, `Quot.sound`, `propext`. This status is decided by Lean and the registry `scripts/trust/headlines.txt`, never by prose: a headline is withdrawn only by removing it from `Checked` and the registry, which removes it from this page. **Fidelity record (generated; what has been machine-checked about what the statement means, not a proof that it matches its source), in two parts. (A) Re-derived by the kernel from the statement; holds whoever wrote the statement, its witnesses and its proofs; shows the statement is not vacuous and which hypotheses matter, not that it says what its source says:** non-vacuity: nothing to witness (the statement has no hypothesis to meet); hypotheses: none numbered; no assumption outside the numbering (`TRUST_MAP.md`, shape); part A complete. **(B) Rests on who wrote a statement; CI checks the route of each item (commit order, briefs without the answer), not that its writer was independent of the authors, so each item is evidence of meaning only as far as that independence holds:** open fidelity objections on record (`scripts/trust/objections.txt`, where every objection to the meaning of a listed headline is entered when it is first written anywhere): none; statement literals: 6 definitions written by a blind second reader of the source are registered for this statement in `scripts/trust/literal_readings.txt` and occur in it (`check_literals.py`) (printed at the head of this line); no literal of the statement is grandfathered as unread (`check_literals.py` requires every other literal to be read twice or certified by the proof); program definitions the claim uses: none. The statement is frozen (`scripts/trust/frozen.txt`): changing it needs a `LEDGER.md` entry naming it (`check_relock.py`), and a changed statement changes the claim on this page. CI regenerates this page on every push and fails if the committed copy differs, so it cannot lag the Lean sources.

**It holds that**

- there is `f : ℝ → ℝ` such that there is `p : ℝ → ℝ` such that there is `q : ℝ → ℝ` such that (for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt f (p η) (Set.Ici 0) η`) and (for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt p (q η) (Set.Ici 0) η`) and (for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt q (-(2 * f η * q η) - 1 + p η ^ 2) (Set.Ici 0) η`) and (`f 0 = 0`) and (`p 0 = 0`) and (`Filter.Tendsto p Filter.atTop (nhds 1)`) and (`1.3119376938 < q 0`) and (`q 0 < 1.3119376939`)

## Author's paraphrase (hand-written; checked only by prose rules)

Homann axisymmetric stagnation-point flow, existence: there is a solution of
f''' + 2 f f'' + 1 − f'² = 0 on [0, ∞) (f has derivative p, p has derivative q, q has derivative
−2 f q − 1 + p², one-sided at 0) with f(0) = 0, p(0) = 0 and p(η) → 1 as η → ∞ whose wall value
q(0) = f''(0) lies strictly between 1.3119376938 and 1.3119376939.

## Formal statement (Lean 4)

```lean
theorem homann_exists : ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(2 * f η * q η) - 1 + p η ^ 2) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
    1.3119376938 < q 0 ∧ q 0 < 1.3119376939 := …
```

## Definitions it uses

Only Mathlib notions.

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Homann/Homann.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 40
