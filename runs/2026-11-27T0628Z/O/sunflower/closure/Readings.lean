import Mathlib

namespace ReaderA

/-!
# Blind reading (reader A): O14 "An exponential bound for sunflowers", Theorem 1.1

Source: `sunflower/sources/intro_lines1-30.tex`.
-/

namespace ReadingO14

open Real

/-- "distinct sets `A_1, …, A_r` form an `r`-sunflower if `A_i ∩ A_j = C` for every `i ≠ j`."
Sets are indexed by `Fin r`; distinctness is injectivity of the indexing. -/
def IsSunflower {α : Type*} [DecidableEq α] (r : ℕ) (A : Fin r → Finset α) : Prop :=
  Function.Injective A ∧ ∃ C : Finset α, ∀ i j : Fin r, i ≠ j → A i ∩ A j = C

/-- A family `F` (a set of finite sets, hence of distinct sets) contains an `r`-sunflower. -/
def ContainsSunflower {α : Type*} [DecidableEq α] (r : ℕ) (F : Set (Finset α)) : Prop :=
  ∃ A : Fin r → Finset α, (∀ i, A i ∈ F) ∧ IsSunflower r A

/-- `M_r(k)`: the largest size of a family of distinct `k`-element sets containing no
`r`-sunflower. The ground set may be arbitrarily large; we take it to be `ℕ` (any finite
family of finite sets can be relabelled into `ℕ`). The supremum is taken in `ℕ∞`, so if
the sizes were unbounded the value would be `⊤` (no junk value). Only finite families are
counted ("size" of a family). -/
noncomputable def M (r k : ℕ) : ℕ∞ :=
  ⨆ (F : Finset (Finset ℕ)) (_ : ∀ A ∈ F, A.card = k)
    (_ : ¬ ContainsSunflower r (F : Set (Finset ℕ))), (F.card : ℕ∞)

/-- Theorem 1.1, qualitative form: for each integer `r ≥ 3` there is a constant `B_r` such
that every family of distinct sets of size at most `k` with no `r`-sunflower has at most
`B_r^k` members, for every integer `k ≥ 1`; in particular `M_r(k) ≤ B_r^k`. -/
theorem reading_O14_qualitative :
    ∀ r : ℕ, 3 ≤ r → ∃ B : ℝ,
      (∀ (α : Type) [DecidableEq α] (F : Set (Finset α)) (k : ℕ), 1 ≤ k →
          (∀ A ∈ F, A.card ≤ k) → ¬ ContainsSunflower r F →
          F.Finite ∧ (F.ncard : ℝ) ≤ B ^ k) ∧
      (∀ k : ℕ, 1 ≤ k → ((M r k : ℕ∞) : ENNReal) ≤ ENNReal.ofReal (B ^ k)) := by
  sorry

/-- `H = log₂(2r)`. -/
noncomputable def H (r : ℕ) : ℝ := Real.logb 2 (2 * (r : ℝ))

/-- `L = log₂(2H)`. -/
noncomputable def L (r : ℕ) : ℝ := Real.logb 2 (2 * H r)

/-- `B_r = 2^{C H⁴ L^{5/2}}`. -/
noncomputable def B (C : ℝ) (r : ℕ) : ℝ := (2 : ℝ) ^ (C * H r ^ 4 * L r ^ ((5 : ℝ) / 2))

/-- Theorem 1.1, quantitative form: there is an absolute constant `C` such that the
conclusion holds for every `r ≥ 3` with `B_r = 2^{C H⁴ L^{5/2}}`. -/
theorem reading_O14_quantitative :
    ∃ C : ℝ, ∀ r : ℕ, 3 ≤ r →
      (∀ (α : Type) [DecidableEq α] (F : Set (Finset α)) (k : ℕ), 1 ≤ k →
          (∀ A ∈ F, A.card ≤ k) → ¬ ContainsSunflower r F →
          F.Finite ∧ (F.ncard : ℝ) ≤ B C r ^ k) ∧
      (∀ k : ℕ, 1 ≤ k → ((M r k : ℕ∞) : ENNReal) ≤ ENNReal.ofReal (B C r ^ k)) := by
  sorry

end ReadingO14

/-!
## Ambiguities and choices (reader A)

1. *Sunflower definition.* The source: "distinct sets `A_1,…,A_r` form an r-sunflower if
   `A_i ∩ A_j = C` for every `i ≠ j`". Encoded as an injective `Fin r → Finset α` with a
   common pairwise intersection `C`. The core `C` is existentially quantified and may be
   empty. Petals are not required to be nonempty beyond distinctness (the source does not
   ask for it).
2. *What a "set" is.* Members have "size at most k", so they are finite: `Finset α`.
3. *Ground set.* "May be arbitrarily large": the theorem quantifies over every ground type
   `α : Type` (universe 0; the bound `B` is chosen before `α`, so it is uniform over ground
   sets). For `M_r(k)` the ground set is fixed to `ℕ`, which loses nothing for finite families.
4. *Family size / finiteness.* A family is a `Set (Finset α)` (so its members are
   automatically distinct). The family is not assumed finite; the conclusion asserts
   `F.Finite` together with `ncard ≤ B^k`, so `ncard`'s junk value `0` for infinite sets
   cannot make the statement vacuous.
5. *`M_r(k)`.* Defined as an `ℕ∞`-valued supremum over finite families of `k`-element
   subsets of `ℕ` without an r-sunflower; no junk (an unbounded supremum would be `⊤`).
   "Largest size" of exact `k`-element families, as stated (not "at most k"). The comparison
   `M_r(k) ≤ B_r^k` is done in `ENNReal` via `ENNReal.ofReal`; since the first conjunct
   already forces `B^k ≥ 1` for `k ≥ 1` (any single `k`-set is a sunflower-free family when
   `r ≥ 3`), `ofReal` truncation at 0 is harmless.
6. *Quantifier order.* Qualitative: `∀ r ≥ 3, ∃ B_r, ∀ k ≥ 1, ∀ family`. Quantitative:
   `∃ C` (absolute: chosen before `r`), then `∀ r ≥ 3` with `B_r` the explicit formula.
   No sign/positivity condition is imposed on `C` (the source says only "absolute constant").
7. *Logarithms and powers.* `log₂` is `Real.logb 2`; `L^{5/2}` is `Real.rpow` with exponent
   `5/2`; for `r ≥ 3`, `H = log₂ 6 > 2` and `L > 2`, so all logs/rpow are at positive
   arguments (no junk). `2^{…}` is real `rpow` with base 2.
8. *"r integer", "k integer".* Both taken in `ℕ` with the stated lower bounds.
9. The ground type is in `Type` (universe 0), not universe-polymorphic; this is a minor
   restriction and changes nothing mathematically.
-/
end ReaderA

namespace ReaderB

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
end ReaderB

namespace ReaderC

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
end ReaderC
