# Item 15

**Area:** Falkner–Skan attached rows β = −0.13, −0.14, −0.15, −0.16

**Source (hand-written: the author's title of the finding or a fixed source line; no check reads it):** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**Status (generated):** **The source's own form, as a blind reader wrote it from the source without seeing this statement (each body occurs in the statement below, `check_literals.py`):** `Checked.Trust.SecondReading.gelfandRhs` := `fun s w φ => -(2 / s * φ s) - Real.exp (w s)`; `Checked.Trust.SecondReading.gelfandCentre` := `fun w => w 0 = 0`; `Checked.Trust.SecondReading.gelfandLambda` := `fun s w => s ^ 2 * Real.exp (w s)`; `Checked.Trust.SecondReading.beHalfLine` := `Set.Ici 0`; `Checked.Trust.SecondReading.beOpenHalfLine` := `Set.Ioi 0`; `Checked.Trust.SecondReading.beFirstMax` := `fun ξ => ξ 0`; `Checked.Trust.SecondReading.beMaxIndex` := `fun k => 2 * k`; `Checked.Trust.SecondReading.beMinIndex` := `fun k => 2 * k + 1`; `Checked.Trust.SecondReading.beNextMaxIndex` := `fun k => 2 * k + 2`; `Checked.Trust.SecondReading.beRiseFromCentre` := `fun ξ => Set.Icc 0 (ξ 0)`; `Checked.Trust.SecondReading.beFallSegment` := `fun ξ k => Set.Icc (ξ (2 * k)) (ξ (2 * k + 1))`; `Checked.Trust.SecondReading.beRiseSegment` := `fun ξ k => Set.Icc (ξ (2 * k + 1)) (ξ (2 * k + 2))`; `Checked.Trust.SecondReading.gelfandSingularLambda` := `2`; `Checked.Trust.SecondReading.gelfandBranchLimit` := `fun w => Filter.Tendsto (fun s => s ^ 2 * Real.exp (w s)) Filter.atTop (nhds 2)`. the statement is proved in module `Checked.Math.GelfandExtrema` of `Checked`; axioms, computed by Lean when this page was generated: `Classical.choice`, `Quot.sound`, `propext`. This status is decided by Lean and the registry `scripts/trust/headlines.txt`, never by prose: a headline is withdrawn only by removing it from `Checked` and the registry, which removes it from this page. **Fidelity record (generated; what has been machine-checked about what the statement means, not a proof that it matches its source), in two parts. (A) Re-derived by the kernel from the statement; holds whoever wrote the statement, its witnesses and its proofs; shows the statement is not vacuous and which hypotheses matter, not that it says what its source says:** non-vacuity: the Checked theorem `Checked.Trust.NV.gelfand_extrema` states the obligation `Checked.Trust.nvObligation` computes from the statement (data exist that meet its hypotheses); hypotheses: 4 numbered; 3 shown needed (a Checked example meets every other hypothesis and the conclusion fails), 1 shown redundant (the statement is proved without it, one at a time), 0 with no obligation (instance or proof used as data), 0 open (per hypothesis: `TRUST_MAP.md`, section "Hypothesis necessity"); no assumption outside the numbering (`TRUST_MAP.md`, shape); part A complete. **(B) Rests on who wrote a statement; CI checks the route of each item (commit order, briefs without the answer), not that its writer was independent of the authors, so each item is evidence of meaning only as far as that independence holds:** open fidelity objections on record (`scripts/trust/objections.txt`, where every objection to the meaning of a listed headline is entered when it is first written anywhere): none; statement literals: 14 definitions written by a blind second reader of the source are registered for this statement in `scripts/trust/literal_readings.txt` and occur in it (`check_literals.py`) (printed at the head of this line); no literal of the statement is grandfathered as unread (`check_literals.py` requires every other literal to be read twice or certified by the proof); program definitions the claim uses: none. The statement is frozen (`scripts/trust/frozen.txt`): changing it needs a `LEDGER.md` entry naming it (`check_relock.py`), and a changed statement changes the claim on this page. CI regenerates this page on every push and fails if the committed copy differs, so it cannot lag the Lean sources.

**For every** `w : ℝ → ℝ`, `φ : ℝ → ℝ`:

**assuming**

1. for every `s : ℝ`, if `s ∈ Set.Ici 0`, then `HasDerivWithinAt w (φ s) (Set.Ici 0) s`
2. `ContinuousWithinAt φ (Set.Ici 0) 0`
3. for every `s : ℝ`, if `s ∈ Set.Ioi 0`, then `HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Set.Ici 0) s`
4. `w 0 = 0`

**then**

- there is `ζ : ℕ → ℝ` such that (`StrictMono ζ`) and (`Filter.Tendsto ζ Filter.atTop Filter.atTop`) and (`4.071496844 ≤ ζ 0`) and (`ζ 0 ≤ 4.071496845`) and (`3.321992118 ≤ ζ 0 ^ 2 * Real.exp (w (ζ 0))`) and (`ζ 0 ^ 2 * Real.exp (w (ζ 0)) ≤ 3.321992119`) and (for every `s : ℝ`, if `s ∈ Set.Ici 0`, then if `s ≠ ζ 0`, then `s ^ 2 * Real.exp (w s) < ζ 0 ^ 2 * Real.exp (w (ζ 0))`) and (for every `k : ℕ`, for every `s : ℝ`, if `s ∈ Set.Ici (ζ (2 * k))`, then if `s ≠ ζ (2 * k + 1)`, then `ζ (2 * k + 1) ^ 2 * Real.exp (w (ζ (2 * k + 1))) < s ^ 2 * Real.exp (w s)`) and (for every `k : ℕ`, for every `s : ℝ`, if `s ∈ Set.Ici (ζ (2 * k + 1))`, then if `s ≠ ζ (2 * k + 2)`, then `s ^ 2 * Real.exp (w s) < ζ (2 * k + 2) ^ 2 * Real.exp (w (ζ (2 * k + 2)))`) and (for every `k : ℕ`, (`ζ (2 * k + 1) ^ 2 * Real.exp (w (ζ (2 * k + 1))) < 2`) and (`2 < ζ (2 * k) ^ 2 * Real.exp (w (ζ (2 * k)))`)) and (`Filter.Tendsto (fun s => s ^ 2 * Real.exp (w s)) Filter.atTop (nhds 2)`) and (`StrictMonoOn (fun s => s ^ 2 * Real.exp (w s)) (Set.Icc 0 (ζ 0))`) and (for every `k : ℕ`, `StrictAntiOn (fun s => s ^ 2 * Real.exp (w s)) (Set.Icc (ζ (2 * k)) (ζ (2 * k + 1)))`) and (for every `k : ℕ`, `StrictMonoOn (fun s => s ^ 2 * Real.exp (w s)) (Set.Icc (ζ (2 * k + 1)) (ζ (2 * k + 2)))`)

## Author's paraphrase (hand-written; checked only by prose rules)

Gelfand problem, turning points of the radial branch: for every
solution w of w'' + (2/s)w' + e^w = 0 on (0, ∞) with w(0) = 0, w differentiable on [0, ∞) with derivative
φ and φ continuous at 0, with λ(s) = s² e^{w(s)}, there is a strictly increasing sequence of radii
ζ(0) < ζ(1) < … tending to infinity, with ζ(0) between 4.071496844 and 4.071496845 and λ(ζ(0)) between
3.321992118 and 3.321992119, such that λ(s) < λ(ζ(0)) for s ≥ 0 with s ≠ ζ(0); for every k,
λ(ζ(2k+1)) < λ(s) for s ≥ ζ(2k) with s ≠ ζ(2k+1), and λ(s) < λ(ζ(2k+2)) for s ≥ ζ(2k+1) with
s ≠ ζ(2k+2); for every k, λ(ζ(2k+1)) < 2 < λ(ζ(2k)); λ(s) tends to 2 as s tends to infinity; and λ is
strictly increasing on [0, ζ(0)], strictly decreasing on [ζ(2k), ζ(2k+1)] and strictly increasing on
[ζ(2k+1), ζ(2k+2)] for every k.

## Formal statement (Lean 4)

```lean
theorem gelfand_extrema (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt w (φ s) (Ici 0) s)
    (hφ0 : ContinuousWithinAt φ (Ici 0) 0)
    (hφ : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Ici 0) s)
    (h0 : w 0 = 0) :
    ∃ ζ : ℕ → ℝ, StrictMono ζ ∧ Tendsto ζ atTop atTop ∧
      4.071496844 ≤ ζ 0 ∧ ζ 0 ≤ 4.071496845 ∧
      3.321992118 ≤ ζ 0 ^ 2 * Real.exp (w (ζ 0)) ∧ ζ 0 ^ 2 * Real.exp (w (ζ 0)) ≤ 3.321992119 ∧
      (∀ s ∈ Ici (0 : ℝ), s ≠ ζ 0 → s ^ 2 * Real.exp (w s) < ζ 0 ^ 2 * Real.exp (w (ζ 0))) ∧
      (∀ k : ℕ, ∀ s ∈ Ici (ζ (2 * k)), s ≠ ζ (2 * k + 1) →
        ζ (2 * k + 1) ^ 2 * Real.exp (w (ζ (2 * k + 1))) < s ^ 2 * Real.exp (w s)) ∧
      (∀ k : ℕ, ∀ s ∈ Ici (ζ (2 * k + 1)), s ≠ ζ (2 * k + 2) →
        s ^ 2 * Real.exp (w s) < ζ (2 * k + 2) ^ 2 * Real.exp (w (ζ (2 * k + 2)))) ∧
      (∀ k : ℕ, ζ (2 * k + 1) ^ 2 * Real.exp (w (ζ (2 * k + 1))) < 2 ∧
        2 < ζ (2 * k) ^ 2 * Real.exp (w (ζ (2 * k)))) ∧
      Tendsto (fun s => s ^ 2 * Real.exp (w s)) atTop (𝓝 2) ∧
      StrictMonoOn (fun s => s ^ 2 * Real.exp (w s)) (Icc 0 (ζ 0)) ∧
      (∀ k : ℕ, StrictAntiOn (fun s => s ^ 2 * Real.exp (w s)) (Icc (ζ (2 * k)) (ζ (2 * k + 1)))) ∧
      (∀ k : ℕ,
        StrictMonoOn (fun s => s ^ 2 * Real.exp (w s)) (Icc (ζ (2 * k + 1)) (ζ (2 * k + 2)))) := …
```

## Definitions it uses

Only Mathlib notions.

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `gelfand_extrema`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Math/GelfandExtrema.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 15
