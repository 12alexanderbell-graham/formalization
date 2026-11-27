import Mathlib

open Set

/-- `S` is an `r`-sunflower: `r` distinct sets with a common core `C`, `A ∩ A' = C` for all distinct pairs. -/
def IsSunflowerOf {α : Type} [DecidableEq α] (r : ℕ) (S : Finset (Finset α)) : Prop :=
  S.card = r ∧ ∃ C : Finset α, ∀ A ∈ S, ∀ A' ∈ S, A ≠ A' → A ∩ A' = C

/-- A family (set of finite sets) contains an `r`-sunflower. -/
def ContainsSunflower {α : Type} [DecidableEq α] (r : ℕ) (F : Set (Finset α)) : Prop :=
  ∃ S : Finset (Finset α), (↑S : Set (Finset α)) ⊆ F ∧ IsSunflowerOf r S

/-- `H = log₂(2r)`. -/
noncomputable def Hh (r : ℕ) : ℝ := Real.logb 2 (2 * (r : ℝ))
/-- `L = log₂(2H)`. -/
noncomputable def Ll (r : ℕ) : ℝ := Real.logb 2 (2 * Hh r)

/-- Qualitative form. -/
theorem reading_sunflower_qualitative :
    ∀ r : ℕ, 3 ≤ r → ∃ B : ℝ, ∀ k : ℕ, 1 ≤ k → ∀ (α : Type) [DecidableEq α] (F : Set (Finset α)),
      (∀ A ∈ F, A.card ≤ k) → ¬ ContainsSunflower r F →
        F.Finite ∧ (F.ncard : ℝ) ≤ B ^ k := sorry

/-- Quantitative form: one absolute `C` works for all `r`, `k`. -/
theorem reading_sunflower_quantitative :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 3 ≤ r → ∀ k : ℕ, 1 ≤ k → ∀ (α : Type) [DecidableEq α] (F : Set (Finset α)),
      (∀ A ∈ F, A.card ≤ k) → ¬ ContainsSunflower r F →
        F.Finite ∧
        (F.ncard : ℝ) ≤ ((2 : ℝ) ^ (C * (Hh r) ^ (4 : ℝ) * (Ll r) ^ ((5 : ℝ) / 2))) ^ k := sorry

/-
Ambiguities / choices:
* "Family of distinct sets": a `Set (Finset α)`; sets are finite since size ≤ k. Ground type `α : Type`
  (universe 0, "arbitrarily large" is arguably only needed up to finite unions; a finite family lives in a
  finite subset anyway). Finiteness of the family is part of the conclusion (so infinite families are covered);
  `ncard` is then the true cardinality.
* r-sunflower: distinct sets A_1..A_r = a Finset of r distinct members contained in F, common pairwise
  intersection C. Core may be empty. For r ≥ 3 only (r ≥ 3 hypothesis); no junk for r<3.
* "sets of size at most k" -> card ≤ k; k ≥ 1 as stated.
* Qualitative: B real (not necessarily integer), depends only on r (quantified before k, α, F).
* Quantitative: C absolute and positive (positivity added; "constant C" otherwise could be negative making
  the claim false/stronger, positivity is the natural reading). Logs base 2 via Real.logb 2. Exponents use
  real rpow: H^4 as H^(4:ℝ) and L^(5/2); H ≥ log2 6 > 0 and L > 0 for r ≥ 3 so no junk values from rpow.
  B_r^k is real power with natural k.
* The source's "In particular M_r(k) ≤ B_r^k" is a corollary and not stated separately.
-/
