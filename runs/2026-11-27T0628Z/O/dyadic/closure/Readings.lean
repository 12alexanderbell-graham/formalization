import Mathlib

namespace ReaderA

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
end ReaderA

namespace ReaderB

open MeasureTheory Set

/-- `D = {2^{-n} : n ∈ ℕ, n ≥ 1}`. -/
def Ddy : Set ℝ := {y | ∃ n : ℕ, 1 ≤ n ∧ y = (2 : ℝ) ^ (-(n : ℤ))}

/-- The affine copy `x + s D = {x + s a : a ∈ D}`. -/
def affCopy (x s : ℝ) (A : Set ℝ) : Set ℝ := {y | ∃ a ∈ A, y = x + s * a}

theorem reading_dyadic_copy :
    ∀ η : ℝ, 0 < η → η < 1 → ∃ E : Set ℝ, IsCompact E ∧ E ⊆ Icc (0 : ℝ) 1 ∧
      ENNReal.ofReal (1 - η) < volume E ∧
      ∀ x s : ℝ, s ≠ 0 → ¬ (affCopy x s Ddy ⊆ E) := sorry

theorem reading_dyadic_equiv :
    ∀ η : ℝ, 0 < η → η < 1 → ∃ E : Set ℝ, IsCompact E ∧ E ⊆ Icc (0 : ℝ) 1 ∧
      ENNReal.ofReal (1 - η) < volume E ∧
      ∀ x s : ℝ, s ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x + s * (2 : ℝ) ^ (-(n : ℤ)) ∉ E := sorry

/-
Ambiguities / choices:
* `m(E) > 1 - η` is `ENNReal.ofReal (1 - η) < volume E` (volume = Lebesgue on ℝ); since η ∈ (0,1), 1-η > 0
  so ofReal does not truncate (no junk).
* ℕ in source includes 0 possibly, hence the explicit n ≥ 1 in D. 2^{-n} as zpow of (2:ℝ) with -(n:ℤ).
* Affine copy defined as a set-builder; nontrivial means s ≠ 0, x arbitrary real.
* Two theorems: first form `x + sD ⊄ E_η` (in terms of D, with ⊆ negated), second the "Equivalently" form
  with an explicit n ≥ 1 witness. Both existentially quantify E before x, s (E depends on η only).
* η ∈ (0,1) as open interval, as in source.
-/
end ReaderB

namespace ReaderC

open MeasureTheory Set

namespace ReadingC

/-- D = {2^{-n} : n ∈ ℕ, n ≥ 1}. -/
def dyD : Set ℝ :=
  {d | ∃ n : ℕ, 1 ≤ n ∧ d = (2 : ℝ) ^ (-(n : ℤ))}

/-- The nontrivial affine copy x + sD = {x + s d : d ∈ D}. -/
def dyAffineCopy (x s : ℝ) : Set ℝ :=
  (fun d : ℝ => x + s * d) '' dyD

/-- Theorem 1.1 (both forms, sharing the same E_η): for every η ∈ (0,1) there is a compact
E_η ⊆ [0,1] with m(E_η) > 1 - η such that
  (i) for every x ∈ ℝ and s ∈ ℝ \ {0}, x + sD ⊄ E_η;
  (ii) (Equivalently) for every such x, s there is n ≥ 1 with x + s 2^{-n} ∉ E_η. -/
theorem reading_dyadic_main :
    ∀ η : ℝ, 0 < η → η < 1 → ∃ E : Set ℝ,
      IsCompact E ∧ E ⊆ Icc (0 : ℝ) 1 ∧
      ENNReal.ofReal (1 - η) < volume E ∧
      (∀ x s : ℝ, s ≠ 0 → ¬ (dyAffineCopy x s ⊆ E)) ∧
      (∀ x s : ℝ, s ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x + s * (2 : ℝ) ^ (-(n : ℤ)) ∉ E) := sorry

end ReadingC

/-
Ambiguities and choices (reader C):

1. D = {2^{-n} : n ∈ ℕ, n ≥ 1} written as a Set ℝ with existential over n : ℕ and 1 ≤ n;
   the power is the ℤ-power 2^(-(n:ℤ)) (zpow), so 2^{-n} is exactly the source's expression.

2. x + sD is the image of D under d ↦ x + s d (as a set, so no multiplicity issues).
   "Nontrivial affine copy" with s ≠ 0 is the hypothesis s ≠ 0 on each universal statement.

3. "x + sD ⊄ E_η" is ¬ (dyAffineCopy x s ⊆ E). Read as: not a subset, i.e. some point of
   x + sD lies outside E_η. Equivalent to clause (ii) by unfolding the image; I kept both.

4. m(E_η) > 1 - η: "m" is Lebesgue measure, so volume on ℝ (MeasureTheory.volume). Measures
   are ENNReal, so the comparison is ENNReal.ofReal (1 - η) < volume E. Since η < 1 we have
   1 - η > 0, so ofReal does not clip the bound (no junk value here).

5. "compact set E_η ⊆ [0,1]": IsCompact E and E ⊆ Icc 0 1.

6. Quantifier scope: E is chosen after η (the source says "for every η there is E_η").
   The η ∈ (0,1) restriction is stated as 0 < η and η < 1.

7. "for every x ∈ ℝ and every s ∈ ℝ \ {0}" is ∀ x s : ℝ, s ≠ 0 → ...; this is literal.

8. Clause (ii) takes n : ℕ with 1 ≤ n, matching n ∈ ℕ, n ≥ 1 in D's definition. The
   source writes "integer n ≥ 1", so ℕ with 1 ≤ n is the literal reading.

9. I bundled both forms into one theorem with a shared E, since the source states one
   theorem about one E_η. The brief asked for both forms as the theorem's content.
-/
end ReaderC
