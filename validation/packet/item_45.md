# Item 45

**Area:** Mathematics

**Source (hand-written: the author's title of the finding or a fixed source line; no check reads it):** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**Status (generated):** **The source's own form, as a blind reader wrote it from the source without seeing this statement (each body occurs in the statement below, `check_literals.py`):** `Checked.Trust.SecondReading.le2Rhs` := `fun θ φ ξ => -(2 / ξ * φ ξ) - θ ξ ^ 2`; `Checked.Trust.SecondReading.le2RangeTyped` := `Set.Icc 0 5`; `Checked.Trust.SecondReading.le2Range` := `Set.Icc 0 5`; `Checked.Trust.SecondReading.le2RangeOpen` := `Set.Ioc 0 5`; `Checked.Trust.SecondReading.le2ContCentre` := `fun φ => ContinuousWithinAt φ (Set.Icc 0 5) 0`; `Checked.Trust.SecondReading.le2Centre` := `fun θ => θ 0 = 1`; `Checked.Trust.SecondReading.le2Before` := `fun θ x => ∀ ξ ∈ Set.Ico 0 x, 0 < θ ξ`; `Checked.Trust.SecondReading.le2Zero` := `fun x => 4.3528745959 ≤ x ∧ x ≤ 4.3528745960`; `Checked.Trust.SecondReading.le2Mass` := `fun x φ => 2.4110460120 ≤ -(x ^ 2 * φ x) ∧ -(x ^ 2 * φ x) ≤ 2.4110460122`; `Checked.Trust.SecondReading.le2Conc` := `fun x φ => 11.402542860 ≤ x ^ 3 / (3 * -(x ^ 2 * φ x)) ∧ x ^ 3 / (3 * -(x ^ 2 * φ x)) ≤ 11.402542864`. the statement is proved in module `Checked.Math.LaneEmden2` of `Checked`; axioms, computed by Lean when this page was generated: `Classical.choice`, `Quot.sound`, `propext`. This status is decided by Lean and the registry `scripts/trust/headlines.txt`, never by prose: a headline is withdrawn only by removing it from `Checked` and the registry, which removes it from this page. **Fidelity record (generated; what has been machine-checked about what the statement means, not a proof that it matches its source):** open fidelity objections on record (`scripts/trust/objections.txt`, where every objection to the meaning of a listed headline is entered when it is first written anywhere): none; non-vacuity: the Checked theorem `Checked.Trust.NV.laneEmden2_constants` states the obligation `Checked.Trust.nvObligation` computes from the statement (data exist that meet its hypotheses); hypotheses: 4 numbered; 3 shown needed (a Checked example meets every other hypothesis and the conclusion fails), 1 shown redundant (the statement is proved without it, one at a time), 0 with no obligation (instance or proof used as data), 0 open (per hypothesis: `TRUST_MAP.md`, section "Hypothesis necessity"); statement literals: 10 definitions written by a blind second reader of the source are registered for this statement in `scripts/trust/literal_readings.txt` and occur in it (`check_literals.py`) (printed at the head of this line); no literal of the statement is grandfathered as unread (`check_literals.py` requires every other literal to be read twice or certified by the proof); the statement is frozen (`scripts/trust/frozen.txt`): changing it needs a `LEDGER.md` entry naming it (`check_relock.py`), and a changed statement changes the claim on this page. CI regenerates this page on every push and fails if the committed copy differs, so it cannot lag the Lean sources.

**For every** `θ : ℝ → ℝ`, `φ : ℝ → ℝ`:

**assuming**

1. for every `ξ : ℝ`, if `ξ ∈ Set.Icc 0 5`, then `HasDerivWithinAt θ (φ ξ) (Set.Icc 0 5) ξ`
2. `ContinuousWithinAt φ (Set.Icc 0 5) 0`
3. for every `ξ : ℝ`, if `ξ ∈ Set.Ioc 0 5`, then `HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ 2) (Set.Icc 0 5) ξ`
4. `θ 0 = 1`

**then**

- there is `ξ₁ : ℝ` such that (`4.3528745959 ≤ ξ₁`) and (`ξ₁ ≤ 4.3528745960`) and (`θ ξ₁ = 0`) and (for every `ξ : ℝ`, if `ξ ∈ Set.Ico 0 ξ₁`, then `0 < θ ξ`) and (`2.4110460120 ≤ -(ξ₁ ^ 2 * φ ξ₁)`) and (`-(ξ₁ ^ 2 * φ ξ₁) ≤ 2.4110460122`) and (`11.402542860 ≤ ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁))`) and (`ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ≤ 11.402542864`)

## Author's paraphrase (hand-written; checked only by prose rules)

Lane–Emden equation θ'' + (2/ξ)θ' + θ² = 0: for every solution θ on (0, 5] with θ(0) = 1, θ
differentiable on [0, 5] with derivative φ, and φ continuous at 0, there is a first zero ξ₁ of θ with
4.3528745959 ≤ ξ₁ ≤ 4.3528745960, at which −ξ₁² θ'(ξ₁) lies between 2.4110460120 and 2.4110460122
and ξ₁³/(3 · (−ξ₁² θ'(ξ₁))) lies between 11.402542860 and 11.402542864.

## Formal statement (Lean 4)

```lean
theorem laneEmden2_constants (θ φ : ℝ → ℝ)
    (hθ : ∀ ξ ∈ Icc (0 : ℝ) 5, HasDerivWithinAt θ (φ ξ) (Icc 0 5) ξ)
    (hφ0 : ContinuousWithinAt φ (Icc 0 5) 0)
    (hφ : ∀ ξ ∈ Ioc (0 : ℝ) 5, HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ 2) (Icc 0 5) ξ)
    (h0 : θ 0 = 1) :
    ∃ ξ₁ : ℝ, 4.3528745959 ≤ ξ₁ ∧ ξ₁ ≤ 4.3528745960 ∧ θ ξ₁ = 0 ∧ (∀ ξ ∈ Ico 0 ξ₁, 0 < θ ξ) ∧
      2.4110460120 ≤ -(ξ₁ ^ 2 * φ ξ₁) ∧ -(ξ₁ ^ 2 * φ ξ₁) ≤ 2.4110460122 ∧
      11.402542860 ≤ ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ∧
      ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ≤ 11.402542864 := …
```

## Definitions it uses

Only Mathlib notions.

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `laneEmden2_constants`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Math/LaneEmden2.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 45
