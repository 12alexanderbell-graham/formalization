# Item 45

**Area:** Mathematics

**Source (hand-written: the author's title of the finding or a fixed source line; no check reads it):** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**Status (generated):** **The source's own form, as a blind reader wrote it from the source without seeing this statement (each body occurs in the statement below, `check_literals.py`):** `Checked.Trust.SecondReading.townesRhs` := `fun r θ φ => -(1 / r * φ r) + θ r - θ r ^ 3`; `Checked.Trust.SecondReading.townesHalfLine` := `Set.Ici 0`; `Checked.Trust.SecondReading.townesOpenHalfLine` := `Set.Ioi 0`; `Checked.Trust.SecondReading.townesRegularHalfLine` := `fun φ => ContinuousWithinAt φ (Set.Ici 0) 0`; `Checked.Trust.SecondReading.townesSlope` := `fun φ => φ 0 = 0`; `Checked.Trust.SecondReading.townesCentre` := `fun θ c => θ 0 = c`; `Checked.Trust.SecondReading.townesInfinity` := `nhds 0`; `Checked.Trust.SecondReading.townesBracket` := `Set.Ioo 2.2062008646 2.2062008647`. the statement is proved in module `Checked.Townes.TownesExists` of `Checked`; axioms, computed by Lean when this page was generated: `Classical.choice`, `Quot.sound`, `propext`. This status is decided by Lean and the registry `scripts/trust/headlines.txt`, never by prose: a headline is withdrawn only by removing it from `Checked` and the registry, which removes it from this page. **Fidelity record (generated; what has been machine-checked about what the statement means, not a proof that it matches its source), in two parts. (A) Re-derived by the kernel from the statement; holds whoever wrote the statement, its witnesses and its proofs; shows the statement is not vacuous and which hypotheses matter, not that it says what its source says:** non-vacuity: nothing to witness (the statement has no hypothesis to meet); hypotheses: none numbered; no assumption outside the numbering (`TRUST_MAP.md`, shape); part A complete. **(B) Rests on who wrote a statement; CI checks the route of each item (commit order, briefs without the answer), not that its writer was independent of the authors, so each item is evidence of meaning only as far as that independence holds:** open fidelity objections on record (`scripts/trust/objections.txt`, where every objection to the meaning of a listed headline is entered when it is first written anywhere): none; statement literals: 8 definitions written by a blind second reader of the source are registered for this statement in `scripts/trust/literal_readings.txt` and occur in it (`check_literals.py`) (printed at the head of this line); no literal of the statement is grandfathered as unread (`check_literals.py` requires every other literal to be read twice or certified by the proof); program definitions the claim uses: none. The statement is frozen (`scripts/trust/frozen.txt`): changing it needs a `LEDGER.md` entry naming it (`check_relock.py`), and a changed statement changes the claim on this page. CI regenerates this page on every push and fails if the committed copy differs, so it cannot lag the Lean sources.

**It holds that**

- there is `c : ℝ` such that (`c ∈ Set.Ioo 2.2062008646 2.2062008647`) and (there is `θ : ℝ → ℝ` such that there is `φ : ℝ → ℝ` such that (`θ 0 = c`) and (`φ 0 = 0`) and (for every `r : ℝ`, if `r ∈ Set.Ici 0`, then `HasDerivWithinAt θ (φ r) (Set.Ici 0) r`) and (`ContinuousWithinAt φ (Set.Ici 0) 0`) and (for every `r : ℝ`, if `r ∈ Set.Ioi 0`, then `HasDerivAt φ (-(1 / r * φ r) + θ r - θ r ^ 3) r`) and (for every `r : ℝ`, if `r ∈ Set.Ici 0`, then `0 < θ r`) and (for every `r : ℝ`, if `r ∈ Set.Ioi 0`, then `φ r < 0`) and (`Filter.Tendsto θ Filter.atTop (nhds 0)`))

## Author's paraphrase (hand-written; checked only by prose rules)

Townes radial equation, existence: there is c in (2.2062008646, 2.2062008647) and a solution
θ of θ'' + (1/r)θ' − θ + θ³ = 0 on (0, ∞) with θ(0) = c, derivative φ on [0, ∞) (one-sided at 0),
φ(0) = 0 and φ continuous at 0, θ positive on [0, ∞), φ negative on (0, ∞) and θ(r) → 0 as
r → ∞.

## Formal statement (Lean 4)

```lean
theorem townes_exists : ∃ c ∈ Ioo (2.2062008646 : ℝ) 2.2062008647, ∃ θ φ : ℝ → ℝ,
    θ 0 = c ∧ φ 0 = 0 ∧
    (∀ r ∈ Ici (0 : ℝ), HasDerivWithinAt θ (φ r) (Ici 0) r) ∧
    ContinuousWithinAt φ (Ici 0) 0 ∧
    (∀ r ∈ Ioi (0 : ℝ), HasDerivAt φ (-(1 / r * φ r) + θ r - θ r ^ 3) r) ∧
    (∀ r ∈ Ici (0 : ℝ), 0 < θ r) ∧ (∀ r ∈ Ioi (0 : ℝ), φ r < 0) ∧
    Tendsto θ atTop (𝓝 0) := …
```

## Definitions it uses

Only Mathlib notions.

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Townes/TownesExists.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 45
