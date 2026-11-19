# Item 05

**Area:** Mathematics

**Source (hand-written: the author's title of the finding or a fixed source line; no check reads it):** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**Status (generated):** **The source's own form, as a blind reader wrote it from the source without seeing this statement (each body occurs in the statement below, `check_literals.py`):** `Checked.Trust.SecondReading.le32Rhs` := `fun θ φ ξ => -(2 / ξ * φ ξ) - θ ξ ^ (3 / 2)`; `Checked.Trust.SecondReading.le32RangeTyped` := `Set.Icc 0 4`; `Checked.Trust.SecondReading.le32Range` := `Set.Icc 0 4`; `Checked.Trust.SecondReading.le32RangeOpen` := `Set.Ioc 0 4`; `Checked.Trust.SecondReading.le32ContCentre` := `fun φ => ContinuousWithinAt φ (Set.Icc 0 4) 0`; `Checked.Trust.SecondReading.le32Centre` := `fun θ => θ 0 = 1`; `Checked.Trust.SecondReading.le32Before` := `fun θ x => ∀ ξ ∈ Set.Ico 0 x, 0 < θ ξ`; `Checked.Trust.SecondReading.le32Zero` := `fun x => 3.65375373 ≤ x ∧ x ≤ 3.65375374`; `Checked.Trust.SecondReading.le32Mass` := `fun x φ => 2.71405511 ≤ -(x ^ 2 * φ x) ∧ -(x ^ 2 * φ x) ≤ 2.71405513`; `Checked.Trust.SecondReading.le32Conc` := `fun x φ => 5.99070450 ≤ x ^ 3 / (3 * -(x ^ 2 * φ x)) ∧ x ^ 3 / (3 * -(x ^ 2 * φ x)) ≤ 5.99070453`. the statement is proved in module `Checked.Math.LaneEmden32` of `Checked`; axioms, computed by Lean when this page was generated: `Classical.choice`, `Quot.sound`, `propext`. This status is decided by Lean and the registry `scripts/trust/headlines.txt`, never by prose: a headline is withdrawn only by removing it from `Checked` and the registry, which removes it from this page. **Fidelity record (generated; what has been machine-checked about what the statement means, not a proof that it matches its source):** open fidelity objections on record (`scripts/trust/objections.txt`, where every objection to the meaning of a listed headline is entered when it is first written anywhere): none; non-vacuity: the Checked theorem `Checked.Trust.NV.laneEmden32_constants` states the obligation `Checked.Trust.nvObligation` computes from the statement (data exist that meet its hypotheses); hypotheses: 4 numbered; 3 shown needed (a Checked example meets every other hypothesis and the conclusion fails), 1 shown redundant (the statement is proved without it, one at a time), 0 with no obligation (instance or proof used as data), 0 open (per hypothesis: `TRUST_MAP.md`, section "Hypothesis necessity"); statement literals: 10 definitions written by a blind second reader of the source are registered for this statement in `scripts/trust/literal_readings.txt` and occur in it (`check_literals.py`) (printed at the head of this line); no literal of the statement is grandfathered as unread (`check_literals.py` requires every other literal to be read twice or certified by the proof); the statement is frozen (`scripts/trust/frozen.txt`): changing it needs a `LEDGER.md` entry naming it (`check_relock.py`), and a changed statement changes the claim on this page. CI regenerates this page on every push and fails if the committed copy differs, so it cannot lag the Lean sources.

**For every** `θ : ℝ → ℝ`, `φ : ℝ → ℝ`:

**assuming**

1. for every `ξ : ℝ`, if `ξ ∈ Set.Icc 0 4`, then `HasDerivWithinAt θ (φ ξ) (Set.Icc 0 4) ξ`
2. `ContinuousWithinAt φ (Set.Icc 0 4) 0`
3. for every `ξ : ℝ`, if `ξ ∈ Set.Ioc 0 4`, then `HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ (3 / 2)) (Set.Icc 0 4) ξ`
4. `θ 0 = 1`

**then**

- there is `ξ₁ : ℝ` such that (`3.65375373 ≤ ξ₁`) and (`ξ₁ ≤ 3.65375374`) and (`θ ξ₁ = 0`) and (for every `ξ : ℝ`, if `ξ ∈ Set.Ico 0 ξ₁`, then `0 < θ ξ`) and (`2.71405511 ≤ -(ξ₁ ^ 2 * φ ξ₁)`) and (`-(ξ₁ ^ 2 * φ ξ₁) ≤ 2.71405513`) and (`5.99070450 ≤ ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁))`) and (`ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ≤ 5.99070453`)

## Author's paraphrase (hand-written; checked only by prose rules)

Lane–Emden equation θ'' + (2/ξ)θ' + θ ^ (3/2) = 0: for every solution θ on (0, 4] with
θ(0) = 1, θ differentiable on [0, 4] with derivative φ, and φ continuous at 0, there is a zero ξ₁ of
θ with 3.65375373 ≤ ξ₁ ≤ 3.65375374 and θ > 0 on [0, ξ₁), at which −ξ₁² θ'(ξ₁) lies between
2.71405511 and 2.71405513 and ξ₁³/(3 · (−ξ₁² θ'(ξ₁))) lies between 5.99070450 and 5.99070453.

## Formal statement (Lean 4)

```lean
theorem laneEmden32_constants (θ φ : ℝ → ℝ)
    (hθ : ∀ ξ ∈ Icc (0 : ℝ) 4, HasDerivWithinAt θ (φ ξ) (Icc 0 4) ξ)
    (hφ0 : ContinuousWithinAt φ (Icc 0 4) 0)
    (hφ : ∀ ξ ∈ Ioc (0 : ℝ) 4,
      HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ ((3 : ℝ) / 2)) (Icc 0 4) ξ)
    (h0 : θ 0 = 1) :
    ∃ ξ₁ : ℝ, 3.65375373 ≤ ξ₁ ∧ ξ₁ ≤ 3.65375374 ∧ θ ξ₁ = 0 ∧ (∀ ξ ∈ Ico 0 ξ₁, 0 < θ ξ) ∧
      2.71405511 ≤ -(ξ₁ ^ 2 * φ ξ₁) ∧ -(ξ₁ ^ 2 * φ ξ₁) ≤ 2.71405513 ∧
      5.99070450 ≤ ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ∧
      ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ≤ 5.99070453 := …
```

## Definitions it uses

Only Mathlib notions.

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `laneEmden32_constants`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Math/LaneEmden32.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 05
