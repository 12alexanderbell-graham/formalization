import Mathlib

namespace ReadingC

universe u

/-- `F` contains an `r`-sunflower: `r` distinct members of `F` whose pairwise
intersections all equal one common core `C`. (Core may be empty.) -/
def HasSunflower {α : Type u} [DecidableEq α] (r : ℕ) (F : Finset (Finset α)) : Prop :=
  ∃ S : Finset (Finset α), S ⊆ F ∧ S.card = r ∧
    ∃ C : Finset α, ∀ A ∈ S, ∀ B ∈ S, A ≠ B → A ∩ B = C

/-- `F` contains no `r`-sunflower. -/
def NoSunflower {α : Type u} [DecidableEq α] (r : ℕ) (F : Finset (Finset α)) : Prop :=
  ¬ HasSunflower r F

/-- H = log₂(2r). -/
noncomputable def sfH (r : ℕ) : ℝ := Real.logb 2 (2 * (r : ℝ))

/-- L = log₂(2H). -/
noncomputable def sfL (r : ℕ) : ℝ := Real.logb 2 (2 * sfH r)

/-- B_r = 2^(C H^4 L^(5/2)) for a constant `C`. -/
noncomputable def sfB (C : ℝ) (r : ℕ) : ℝ :=
  (2 : ℝ) ^ (C * sfH r ^ 4 * sfL r ^ ((5 : ℝ) / 2))

/-- M_r(k): largest size of a family of distinct k-element sets (ground set ℕ, which
suffices since any finite configuration embeds in ℕ) with no r-sunflower. -/
noncomputable def sfM (r k : ℕ) : ℕ :=
  sSup {n : ℕ | ∃ F : Finset (Finset ℕ), F.card = n ∧ (∀ A ∈ F, A.card = k) ∧ NoSunflower r F}

/-- Qualitative form of Theorem 1.1: for each r ≥ 3 there is a constant B_r, independent of
the ground set, such that every family of distinct sets of size at most k with no
r-sunflower has at most B_r^k members, for every k ≥ 1. -/
theorem reading_sunflower_qualitative :
    ∀ r : ℕ, 3 ≤ r → ∃ B : ℝ, ∀ (α : Type u) [DecidableEq α] (k : ℕ), 1 ≤ k →
      ∀ F : Finset (Finset α), (∀ A ∈ F, A.card ≤ k) → NoSunflower r F →
        (F.card : ℝ) ≤ B ^ k := sorry

/-- Quantitative form of Theorem 1.1: one may take B_r = 2^(C H^4 L^(5/2)) with C absolute. -/
theorem reading_sunflower_quantitative :
    ∃ C : ℝ, ∀ r : ℕ, 3 ≤ r → ∀ (α : Type u) [DecidableEq α] (k : ℕ), 1 ≤ k →
      ∀ F : Finset (Finset α), (∀ A ∈ F, A.card ≤ k) → NoSunflower r F →
        (F.card : ℝ) ≤ (sfB C r) ^ k := sorry

/-- The stated consequence M_r(k) ≤ B_r^k (with the quantitative B_r). -/
theorem reading_sunflower_M_bound :
    ∃ C : ℝ, ∀ r : ℕ, 3 ≤ r → ∀ k : ℕ, 1 ≤ k → (sfM r k : ℝ) ≤ (sfB C r) ^ k := sorry

end ReadingC

/-
Ambiguities and choices (reader C):

1. "Distinct sets A_1..A_r form an r-sunflower if A_i ∩ A_j = C for every i ≠ j".
   Read as: S ⊆ F with S.card = r (so the r sets are distinct), common core C : Finset α
   possibly empty. The ordering of A_i is irrelevant, so I quantify over a set S.

2. "family of distinct sets of size at most k": modelled as a Finset (Finset α), which
   gives distinctness for free. "Size at most k" is A.card ≤ k.

3. Ground set: "may be arbitrarily large". Qualitative form quantifies over all
   α : Type u with DecidableEq, placed AFTER the existential B so B_r does not depend on α.
   Universe fixed to u (single universe variable).

4. "for every integer k ≥ 1": k : ℕ with 1 ≤ k.

5. "r ≥ 3": hypothesis 3 ≤ r with r : ℕ. For r < 3 nothing is claimed.

6. "B_r" is only asserted to exist; no positivity is asserted (none in source).
   In the quantitative form B = 2^(...) is positive automatically.

7. Logs: H = log₂(2r) written as Real.logb 2 (2 * r) with r cast to ℝ; L = log₂(2H)
   as Real.logb 2 (2 * H). Exponent 5/2 is the real number (5:ℝ)/2 and the power of L is
   Real.rpow (L ≥ 0 for r ≥ 3, so no junk issue). H^4 is ℕ-power. The whole exponent of 2
   is a real, so (2:ℝ) ^ (real) is rpow.

8. "C is an absolute constant": ∃ C : ℝ placed before ∀ r, so it is independent of r, α,
   k, F. C is not claimed to be positive or natural; the statement is literal.

9. M_r(k) is defined as sSup of cardinalities over families of k-sets over ℕ. The source
   does not say which ground set; I chose ℕ (infinite, so every finite configuration fits).
   sSup over ℕ returns 0 for an unbounded set (junk value), but the bound statement
   asserts boundedness implicitly; I did not add a separate boundedness claim.
   The "In particular M_r(k) ≤ B_r^k" is an extra theorem (reading_sunflower_M_bound),
   derived in the source from the main bound, with the quantitative B.

10. The source's "one may take B_r = ..." is read as: the quantitative theorem asserts
    the qualitative bound holds with that specific B_r. I wrote both as separate theorems
    rather than an implication.
-/
