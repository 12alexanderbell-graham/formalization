import Mathlib

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
