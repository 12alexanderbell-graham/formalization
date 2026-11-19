# Item 29

**Area:** Mathematics

**Source (hand-written: the author's title of the finding or a fixed source line; no check reads it):** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**Status (generated):** **The source's own form, as a blind reader wrote it from the source without seeing this statement (each body occurs in the statement below, `check_literals.py`):** `Checked.Trust.SecondReading.townesRhs` := `fun r θ φ => -(1 / r * φ r) + θ r - θ r ^ 3`; `Checked.Trust.SecondReading.townesDomain` := `fun S => Set.Icc 0 S`; `Checked.Trust.SecondReading.townesPunctured` := `fun S => Set.Ioc 0 S`; `Checked.Trust.SecondReading.townesRegular` := `fun φ S => ContinuousWithinAt φ (Set.Icc 0 S) 0`; `Checked.Trust.SecondReading.townesUnderStart` := `fun θ => θ 0 = 2.2062008646`; `Checked.Trust.SecondReading.townesHorizon` := `Set.Ioc 0 (68 / 5)`. the statement is proved in module `Checked.Townes.TownesShooting` of `Checked`; axioms, computed by Lean when this page was generated: `Classical.choice`, `Quot.sound`, `propext`. This status is decided by Lean and the registry `scripts/trust/headlines.txt`, never by prose: a headline is withdrawn only by removing it from `Checked` and the registry, which removes it from this page. **Fidelity record (generated; what has been machine-checked about what the statement means, not a proof that it matches its source):** open fidelity objections on record (`scripts/trust/objections.txt`, where every objection to the meaning of a listed headline is entered when it is first written anywhere): none; non-vacuity: the Checked theorem `Checked.Trust.NV.townes_under` states the obligation `Checked.Trust.nvObligation` computes from the statement (data exist that meet its hypotheses); hypotheses: 5 numbered; 4 shown needed (a Checked example meets every other hypothesis and the conclusion fails), 1 shown redundant (the statement is proved without it, one at a time), 0 with no obligation (instance or proof used as data), 0 open (per hypothesis: `TRUST_MAP.md`, section "Hypothesis necessity"); statement literals: 6 definitions written by a blind second reader of the source are registered for this statement in `scripts/trust/literal_readings.txt` and occur in it (`check_literals.py`) (printed at the head of this line); no literal of the statement is grandfathered as unread (`check_literals.py` requires every other literal to be read twice or certified by the proof); the statement is frozen (`scripts/trust/frozen.txt`): changing it needs a `LEDGER.md` entry naming it (`check_relock.py`), and a changed statement changes the claim on this page. CI regenerates this page on every push and fails if the committed copy differs, so it cannot lag the Lean sources.

**For every** `S : ℝ`, `θ : ℝ → ℝ`, `φ : ℝ → ℝ`:

**assuming**

1. `68 / 5 ≤ S`
2. for every `r : ℝ`, if `r ∈ Set.Icc 0 S`, then `HasDerivWithinAt θ (φ r) (Set.Icc 0 S) r`
3. `ContinuousWithinAt φ (Set.Icc 0 S) 0`
4. for every `r : ℝ`, if `r ∈ Set.Ioc 0 S`, then `HasDerivWithinAt φ (-(1 / r * φ r) + θ r - θ r ^ 3) (Set.Icc 0 S) r`
5. `θ 0 = 2.2062008646`

**then**

- there is `r : ℝ` such that (`r ∈ Set.Ioc 0 (68 / 5)`) and (`0 < φ r`) and (for every `s : ℝ`, if `s ∈ Set.Icc 0 r`, then `0 < θ s`)

## Author's paraphrase (hand-written; checked only by prose rules)

Townes radial equation, undershoot: for every S ≥ 68/5 and every solution θ of
θ'' + (1/r)θ' − θ + θ³ = 0 on (0, S] with θ(0) = 2.2062008646, θ differentiable on [0, S] with
derivative φ and φ continuous at 0, there is r in (0, 68/5] with φ(r) > 0 and θ positive on
[0, r].

## Formal statement (Lean 4)

```lean
theorem townes_under (S : ℝ) (hS : 68 / 5 ≤ S) (θ φ : ℝ → ℝ)
    (hθ : ∀ r ∈ Icc (0 : ℝ) S, HasDerivWithinAt θ (φ r) (Icc 0 S) r)
    (hφ0 : ContinuousWithinAt φ (Icc 0 S) 0)
    (hφ : ∀ r ∈ Ioc (0 : ℝ) S, HasDerivWithinAt φ (-(1 / r * φ r) + θ r - θ r ^ 3) (Icc 0 S) r)
    (h0 : θ 0 = 2.2062008646) :
    ∃ r ∈ Ioc (0 : ℝ) (68 / 5), 0 < φ r ∧ ∀ s ∈ Icc 0 r, 0 < θ s := …
```

## Definitions it uses

Only Mathlib notions.

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `townes_under`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Townes/TownesShooting.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 29
