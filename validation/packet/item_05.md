# Item 05

**Area:** Astrophysics

**Source (hand-written: the author's title of the finding or a fixed source line; no check reads it):** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `S : ℝ`, `w : ℝ → ℝ`, `φ : ℝ → ℝ`:

**assuming**

1. `7 ≤ S`
2. for every `s : ℝ`, if `s ∈ Set.Icc 0 S`, then `HasDerivWithinAt w (φ s) (Set.Icc 0 S) s`
3. `ContinuousWithinAt φ (Set.Icc 0 S) 0`
4. for every `s : ℝ`, if `s ∈ Set.Ioc 0 S`, then `HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Set.Icc 0 S) s`
5. `w 0 = 0`

**then**

- there is `ξ₁ : ℝ` such that (`6.4507514 ≤ ξ₁`) and (`ξ₁ ≤ 6.4507515`) and (for every `s : ℝ`, if `s ∈ Set.Icc 0 S`, then if `s ≠ ξ₁`, then `s ^ 2 * -φ s * Real.exp (w s / 2) / √(4 * Real.pi) < ξ₁ ^ 2 * -φ ξ₁ * Real.exp (w ξ₁ / 2) / √(4 * Real.pi)`) and (`1.1822265 ≤ ξ₁ ^ 2 * -φ ξ₁ * Real.exp (w ξ₁ / 2) / √(4 * Real.pi)`) and (`ξ₁ ^ 2 * -φ ξ₁ * Real.exp (w ξ₁ / 2) / √(4 * Real.pi) ≤ 1.1822266`)

## Author's paraphrase (hand-written; checked only by prose rules)

Bonnor–Ebert critical sphere, max of the mass: for every S ≥ 7 and every solution w of
w'' + (2/s)w' + e^w = 0 on (0, S] with w(0) = 0, w differentiable on [0, S] with derivative φ and φ continuous
at 0, there is a radius ξ₁ between 6.4507514 and 6.4507515 such that the dimensionless mass
m(s) = s² (−φ(s)) e^{w(s)/2} / √(4π) has m(s) < m(ξ₁) for s in [0, S] with s ≠ ξ₁;
and m(ξ₁) lies between 1.1822265 and 1.1822266.

## Formal statement (Lean 4)

```lean
theorem bonnor_ebert_max (S : ℝ) (hS : 7 ≤ S) (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt w (φ s) (Icc 0 S) s)
    (hφ0 : ContinuousWithinAt φ (Icc 0 S) 0)
    (hφ : ∀ s ∈ Ioc (0 : ℝ) S,
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 S) s)
    (h0 : w 0 = 0) :
    ∃ ξ₁ : ℝ, 6.4507514 ≤ ξ₁ ∧ ξ₁ ≤ 6.4507515 ∧
      (∀ s ∈ Icc (0 : ℝ) S, s ≠ ξ₁ →
        s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) <
          ξ₁ ^ 2 * (-φ ξ₁) * Real.exp (w ξ₁ / 2) / Real.sqrt (4 * Real.pi)) ∧
      1.1822265 ≤ ξ₁ ^ 2 * (-φ ξ₁) * Real.exp (w ξ₁ / 2) / Real.sqrt (4 * Real.pi) ∧
      ξ₁ ^ 2 * (-φ ξ₁) * Real.exp (w ξ₁ / 2) / Real.sqrt (4 * Real.pi) ≤ 1.1822266 := …
```

## Definitions it uses

Only Mathlib notions.

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `bonnor_ebert_max`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Math/BonnorEbertMax.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 05
