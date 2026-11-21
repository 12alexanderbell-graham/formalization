# Item 34

**Area:** Falkner–Skan attached rows β = −0.13, −0.14, −0.15, −0.16

**Source (hand-written: the author's title of the finding or a fixed source line; no check reads it):** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**Status (generated):** **The source's own form, as a blind reader wrote it from the source without seeing this statement (each body occurs in the statement below, `check_literals.py`):** `Checked.Trust.SecondReading.gelfandRhs` := `fun s w φ => -(2 / s * φ s) - Real.exp (w s)`; `Checked.Trust.SecondReading.gelfandCentre` := `fun w => w 0 = 0`; `Checked.Trust.SecondReading.beMass` := `fun s w φ => s ^ 2 * -φ s * Real.exp (w s / 2) / √(4 * Real.pi)`; `Checked.Trust.SecondReading.beHalfLine` := `Set.Ici 0`; `Checked.Trust.SecondReading.beOpenHalfLine` := `Set.Ioi 0`; `Checked.Trust.SecondReading.beMassSeq` := `fun ξ n w φ => ξ n ^ 2 * -φ (ξ n) * Real.exp (w (ξ n) / 2) / √(4 * Real.pi)`; `Checked.Trust.SecondReading.beFirstMax` := `fun ξ => ξ 0`; `Checked.Trust.SecondReading.beMaxIndex` := `fun k => 2 * k`; `Checked.Trust.SecondReading.beMinIndex` := `fun k => 2 * k + 1`; `Checked.Trust.SecondReading.beNextMaxIndex` := `fun k => 2 * k + 2`; `Checked.Trust.SecondReading.beSingularMass` := `√(2 / Real.pi)`. the statement is proved in module `Checked.Math.BonnorEbertExtrema` of `Checked`; axioms, computed by Lean when this page was generated: `Classical.choice`, `Quot.sound`, `propext`. This status is decided by Lean and the registry `scripts/trust/headlines.txt`, never by prose: a headline is withdrawn only by removing it from `Checked` and the registry, which removes it from this page. **Fidelity record (generated; what has been machine-checked about what the statement means, not a proof that it matches its source):** open fidelity objections on record (`scripts/trust/objections.txt`, where every objection to the meaning of a listed headline is entered when it is first written anywhere): none; non-vacuity: the Checked theorem `Checked.Trust.NV.bonnor_ebert_extrema` states the obligation `Checked.Trust.nvObligation` computes from the statement (data exist that meet its hypotheses); hypotheses: 4 numbered; 3 shown needed (a Checked example meets every other hypothesis and the conclusion fails), 1 shown redundant (the statement is proved without it, one at a time), 0 with no obligation (instance or proof used as data), 0 open (per hypothesis: `TRUST_MAP.md`, section "Hypothesis necessity"); statement literals: 11 definitions written by a blind second reader of the source are registered for this statement in `scripts/trust/literal_readings.txt` and occur in it (`check_literals.py`) (printed at the head of this line); no literal of the statement is grandfathered as unread (`check_literals.py` requires every other literal to be read twice or certified by the proof); the statement is frozen (`scripts/trust/frozen.txt`): changing it needs a `LEDGER.md` entry naming it (`check_relock.py`), and a changed statement changes the claim on this page. CI regenerates this page on every push and fails if the committed copy differs, so it cannot lag the Lean sources.

**For every** `w : ℝ → ℝ`, `φ : ℝ → ℝ`:

**assuming**

1. for every `s : ℝ`, if `s ∈ Set.Ici 0`, then `HasDerivWithinAt w (φ s) (Set.Ici 0) s`
2. `ContinuousWithinAt φ (Set.Ici 0) 0`
3. for every `s : ℝ`, if `s ∈ Set.Ioi 0`, then `HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Set.Ici 0) s`
4. `w 0 = 0`

**then**

- there is `ξ : ℕ → ℝ` such that (`StrictMono ξ`) and (`Filter.Tendsto ξ Filter.atTop Filter.atTop`) and (`6.4507514 ≤ ξ 0`) and (`ξ 0 ≤ 6.4507515`) and (for every `s : ℝ`, if `s ∈ Set.Ici 0`, then if `s ≠ ξ 0`, then `s ^ 2 * -φ s * Real.exp (w s / 2) / √(4 * Real.pi) < ξ 0 ^ 2 * -φ (ξ 0) * Real.exp (w (ξ 0) / 2) / √(4 * Real.pi)`) and (for every `k : ℕ`, for every `s : ℝ`, if `s ∈ Set.Ici (ξ (2 * k))`, then if `s ≠ ξ (2 * k + 1)`, then `ξ (2 * k + 1) ^ 2 * -φ (ξ (2 * k + 1)) * Real.exp (w (ξ (2 * k + 1)) / 2) / √(4 * Real.pi) < s ^ 2 * -φ s * Real.exp (w s / 2) / √(4 * Real.pi)`) and (for every `k : ℕ`, for every `s : ℝ`, if `s ∈ Set.Ici (ξ (2 * k + 1))`, then if `s ≠ ξ (2 * k + 2)`, then `s ^ 2 * -φ s * Real.exp (w s / 2) / √(4 * Real.pi) < ξ (2 * k + 2) ^ 2 * -φ (ξ (2 * k + 2)) * Real.exp (w (ξ (2 * k + 2)) / 2) / √(4 * Real.pi)`) and (for every `k : ℕ`, (`ξ (2 * k + 1) ^ 2 * -φ (ξ (2 * k + 1)) * Real.exp (w (ξ (2 * k + 1)) / 2) / √(4 * Real.pi) < √(2 / Real.pi)`) and (`√(2 / Real.pi) < ξ (2 * k) ^ 2 * -φ (ξ (2 * k)) * Real.exp (w (ξ (2 * k)) / 2) / √(4 * Real.pi)`)) and (`Filter.Tendsto (fun s => s ^ 2 * -φ s * Real.exp (w s / 2) / √(4 * Real.pi)) Filter.atTop (nhds √(2 / Real.pi))`)

## Author's paraphrase (hand-written; checked only by prose rules)

Bonnor–Ebert sphere, extrema of the mass: for every solution w of w'' + (2/s)w' + e^w = 0 on
(0, ∞) with w(0) = 0, w differentiable on [0, ∞) with derivative φ and φ continuous at 0, with
m(s) = s² (−φ(s)) e^{w(s)/2} / √(4π), there is a strictly increasing sequence of radii ξ(0) < ξ(1) < …
tending to infinity, with ξ(0) between 6.4507514 and 6.4507515, such that m(s) < m(ξ(0)) for s ≥ 0 with
s ≠ ξ(0); for every k, m(ξ(2k+1)) < m(s) for s ≥ ξ(2k) with s ≠ ξ(2k+1), and m(s) < m(ξ(2k+2)) for
s ≥ ξ(2k+1) with s ≠ ξ(2k+2); for every k, m(ξ(2k+1)) < √(2/π) < m(ξ(2k)); and m(s) tends to √(2/π) as
s tends to infinity.

## Formal statement (Lean 4)

```lean
theorem bonnor_ebert_extrema (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt w (φ s) (Ici 0) s)
    (hφ0 : ContinuousWithinAt φ (Ici 0) 0)
    (hφ : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Ici 0) s)
    (h0 : w 0 = 0) :
    ∃ ξ : ℕ → ℝ, StrictMono ξ ∧ Tendsto ξ atTop atTop ∧
      6.4507514 ≤ ξ 0 ∧ ξ 0 ≤ 6.4507515 ∧
      (∀ s ∈ Ici (0 : ℝ), s ≠ ξ 0 →
        s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) <
          ξ 0 ^ 2 * (-φ (ξ 0)) * Real.exp (w (ξ 0) / 2) / Real.sqrt (4 * Real.pi)) ∧
      (∀ k : ℕ, ∀ s ∈ Ici (ξ (2 * k)), s ≠ ξ (2 * k + 1) →
        ξ (2 * k + 1) ^ 2 * (-φ (ξ (2 * k + 1))) * Real.exp (w (ξ (2 * k + 1)) / 2) /
            Real.sqrt (4 * Real.pi) <
          s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)) ∧
      (∀ k : ℕ, ∀ s ∈ Ici (ξ (2 * k + 1)), s ≠ ξ (2 * k + 2) →
        s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) <
          ξ (2 * k + 2) ^ 2 * (-φ (ξ (2 * k + 2))) * Real.exp (w (ξ (2 * k + 2)) / 2) /
            Real.sqrt (4 * Real.pi)) ∧
      (∀ k : ℕ,
        ξ (2 * k + 1) ^ 2 * (-φ (ξ (2 * k + 1))) * Real.exp (w (ξ (2 * k + 1)) / 2) /
            Real.sqrt (4 * Real.pi) < Real.sqrt (2 / Real.pi) ∧
        Real.sqrt (2 / Real.pi) <
          ξ (2 * k) ^ 2 * (-φ (ξ (2 * k))) * Real.exp (w (ξ (2 * k)) / 2) / Real.sqrt (4 * Real.pi)) ∧
      Tendsto (fun s => s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)) atTop
        (𝓝 (Real.sqrt (2 / Real.pi))) := …
```

## Definitions it uses

Only Mathlib notions.

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `bonnor_ebert_extrema`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Math/BonnorEbertExtrema.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 34
