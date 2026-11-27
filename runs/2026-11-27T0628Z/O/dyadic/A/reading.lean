import Mathlib

/-!
# Blind reading (reader A): O16 "The dyadic case of the Erdős similarity conjecture",
Theorem 1.1

Source: `dyadic/sources/introduction_lines1-34.tex`.
-/

namespace ReadingO16

open MeasureTheory Set

/-- The affine copy `x + sA = {x + s a : a ∈ A}` (nontrivial when `s ≠ 0`). -/
def affineCopy (x s : ℝ) (A : Set ℝ) : Set ℝ := (fun a => x + s * a) '' A

/-- `A` is measure universal: every Lebesgue-measurable subset of `ℝ` of positive measure
contains a nontrivial affine copy of `A`. (Context only; not used by the theorem.) -/
def MeasureUniversal (A : Set ℝ) : Prop :=
  ∀ E : Set ℝ, MeasurableSet E → 0 < volume E →
    ∃ x s : ℝ, s ≠ 0 ∧ affineCopy x s A ⊆ E

/-- `D = {2^{-n} : n ∈ ℕ, n ≥ 1}`. -/
def D : Set ℝ := {y | ∃ n : ℕ, 1 ≤ n ∧ y = (2 : ℝ) ^ (-(n : ℤ))}

/-- Theorem 1.1, first form: for every `η ∈ (0,1)` there is a compact `E_η ⊆ [0,1]` with
`m(E_η) > 1 - η` such that `x + sD ⊄ E_η` for every `x ∈ ℝ`, `s ∈ ℝ \ {0}`. -/
theorem reading_O16 :
    ∀ η : ℝ, η ∈ Ioo (0 : ℝ) 1 → ∃ E : Set ℝ, IsCompact E ∧ E ⊆ Icc (0 : ℝ) 1 ∧
      ENNReal.ofReal (1 - η) < volume E ∧
      ∀ x s : ℝ, s ≠ 0 → ¬ (affineCopy x s D ⊆ E) := by
  sorry

/-- Theorem 1.1, "Equivalently" form: for every such `x, s` there is an integer `n ≥ 1`
with `x + s 2^{-n} ∉ E_η`. -/
theorem reading_O16_equiv :
    ∀ η : ℝ, η ∈ Ioo (0 : ℝ) 1 → ∃ E : Set ℝ, IsCompact E ∧ E ⊆ Icc (0 : ℝ) 1 ∧
      ENNReal.ofReal (1 - η) < volume E ∧
      ∀ x s : ℝ, s ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x + s * (2 : ℝ) ^ (-(n : ℤ)) ∉ E := by
  sorry

end ReadingO16

/-!
## Ambiguities and choices (reader A)

1. *`D`.* `{2^{-n} : n ∈ ℕ, n ≥ 1}` — the source writes `n ∈ ℕ, n ≥ 1` explicitly, so
   `n = 0` (the point `1`) is excluded regardless of whether `ℕ` contains 0. `2^{-n}` is
   the integer power `zpow` of `(2:ℝ)` at `-n`.
2. *Measure.* `m` is `MeasureTheory.volume` on `ℝ` (Lebesgue). `m(E_η) > 1 - η` is compared
   in `ENNReal` via `ENNReal.ofReal (1 - η)`; since `η < 1`, `1 - η > 0`, so the truncation
   of `ofReal` at 0 never bites (no junk). `E_η ⊆ [0,1]` makes its measure finite anyway.
3. *Compactness / containment.* `IsCompact E` and `E ⊆ Icc 0 1`, as stated.
4. *Affine copy.* `x + sD` is the image of `D` under `a ↦ x + s a`; nontriviality `s ≠ 0`
   is a hypothesis on `s`; `x` ranges over all of `ℝ`.
5. *Two forms.* Stated as two theorems with the same quantifier shape; `E_η` is chosen inside
   each (the source's "Equivalently" refers to the same set, and for a fixed `E` the two
   conclusions are trivially equivalent, so stating them separately loses nothing).
6. `MeasureUniversal` is included only to record the source's definitions; Theorem 1.1 does
   not assert anything about it (it implies `D` is not measure universal, which the source
   does not state in the theorem).
-/
