import Mathlib

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
