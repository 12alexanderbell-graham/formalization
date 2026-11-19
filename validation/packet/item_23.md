# Item 23

**Area:** Mathematics

**Source (hand-written: the author's title of the finding or a fixed source line; no check reads it):** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**Status (generated):** **The source's own form, as a blind reader wrote it from the source without seeing this statement (each body occurs in the statement below, `check_literals.py`):** `Checked.Trust.SecondReading.gelfandPdeSpace` := `EuclideanSpace ℝ (Fin 3)`; `Checked.Trust.SecondReading.gelfandPdeBall` := `Metric.ball 0 1`; `Checked.Trust.SecondReading.gelfandPdeClosedBall` := `Metric.closedBall 0 1`; `Checked.Trust.SecondReading.gelfandPdeRegular` := `fun u => ContDiffOn ℝ 2 u (Metric.ball 0 1)`; `Checked.Trust.SecondReading.gelfandPdeContinuous` := `fun u => ContinuousOn u (Metric.closedBall 0 1)`. the statement is proved in module `Checked.Math.GelfandPDE` of `Checked`; axioms, computed by Lean when this page was generated: `Classical.choice`, `Quot.sound`, `propext`. This status is decided by Lean and the registry `scripts/trust/headlines.txt`, never by prose: a headline is withdrawn only by removing it from `Checked` and the registry, which removes it from this page. **Fidelity record (generated; what has been machine-checked about what the statement means, not a proof that it matches its source):** open fidelity objections on record (`scripts/trust/objections.txt`, where every objection to the meaning of a listed headline is entered when it is first written anywhere): none; non-vacuity: the Checked theorem `Checked.Trust.NV.gelfand_pde_radial_bound` states the obligation `Checked.Trust.nvObligation` computes from the statement (data exist that meet its hypotheses); hypotheses: 5 numbered; 3 shown needed (a Checked example meets every other hypothesis and the conclusion fails), 0 shown redundant (the statement is proved without it, one at a time), 0 with no obligation (instance or proof used as data), 2 open (per hypothesis: `TRUST_MAP.md`, section "Hypothesis necessity"); statement literals: 5 definitions written by a blind second reader of the source are registered for this statement in `scripts/trust/literal_readings.txt` and occur in it (`check_literals.py`) (printed at the head of this line); no literal of the statement is grandfathered as unread (`check_literals.py` requires every other literal to be read twice or certified by the proof); the statement is frozen (`scripts/trust/frozen.txt`): changing it needs a `LEDGER.md` entry naming it (`check_relock.py`), and a changed statement changes the claim on this page. CI regenerates this page on every push and fails if the committed copy differs, so it cannot lag the Lean sources.

**For every** `lam : ℝ`, `u : EuclideanSpace ℝ (Fin 3) → ℝ`:

**assuming**

1. `ContDiffOn ℝ 2 u (Metric.ball 0 1)`
2. `ContinuousOn u (Metric.closedBall 0 1)`
3. for every `x : EuclideanSpace ℝ (Fin 3)`, if `‖x‖ = 1`, then `u x = 0`
4. there is `g : ℝ → ℝ` such that for every `x : EuclideanSpace ℝ (Fin 3)`, if `x ∈ Metric.closedBall 0 1`, then `u x = g ‖x‖`
5. for every `x : EuclideanSpace ℝ (Fin 3)`, if `x ∈ Metric.ball 0 1`, then `Laplacian.laplacian u x + lam * Real.exp (u x) = 0`

**then**

- `lam ≤ 3.321992119`

## Author's paraphrase (hand-written; checked only by prose rules)

Gelfand problem in the unit ball of three-dimensional space, radial solutions: if u is twice
continuously differentiable on the open unit ball, continuous on the closed unit ball, zero on the unit sphere
and a function of ‖x‖ on the closed ball, and Δu + λ eᵘ = 0 on the open ball (Δ is Mathlib's Laplacian),
then λ ≤ 3.321992119.

## Formal statement (Lean 4)

```lean
theorem gelfand_pde_radial_bound (lam : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hu : ContDiffOn ℝ 2 u (ball 0 1))
    (hc : ContinuousOn u (closedBall 0 1))
    (hb : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0)
    (hrad : ∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖)
    (hpde : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0) :
    lam ≤ 3.321992119 := …
```

## Definitions it uses

Only Mathlib notions.

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `gelfand_pde_radial_bound`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Math/GelfandPDE.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 23
