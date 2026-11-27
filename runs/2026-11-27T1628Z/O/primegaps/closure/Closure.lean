import Mathlib
import Readings.primegaps
import ComparatorChallenges.PrimeGaps

/-! # Target O, family O56 (positive lower density of large prime gaps): closures (run 2026-11-27T1628Z).

Frozen statement `OAI.Problem344.large_gaps_and_ratio_density` (taken by name, never retyped): the count bound of
Theorem 1.1 for every `C > 0` with the frozen `largeGapIndices`, and `0 < lowerAsymptoticDensity
ratioIncreaseIndices`, the density as an `sSup` of eventual lower bounds.

Links proved here:
* primes: the frozen `prime n = Nat.nth Nat.Prime (n - 1)` (ℕ subtraction; only `n ≥ 1` is ever used); reader A's
  `p (n + 1) = Nat.nth Nat.Prime n`; readers B and C quantify over any `p` that enumerates the primes increasingly
  from index 1, and every such `p` agrees with `Nat.nth` on `n ≥ 1` (`enum_eq`, by Mathlib's uniqueness of `nth`).
  The enumeration hypotheses are satisfiable (`nth_enum`), so B's and C's readings are not vacuous.
* counts: on `Finset.Icc 1 N` the readers' and the frozen filters agree (only indices `n ≥ 1`).
* density: the frozen `sSup {d | eventually d ≤ ratio}` positive gives some `d > 0` that is eventually below the
  ratio, hence below the readers' `liminf` (the ratio is bounded by 1, so the real `liminf` is not junk). -/

namespace TargetO.PrimeGaps

open Filter OAI

/-! ## The prime enumeration -/

theorem primes_infinite : (Set.ofPred Nat.Prime).Infinite := Nat.infinite_setOfPred_prime

/-- Any increasing enumeration of the primes from index 1 agrees with `Nat.nth` there. -/
theorem enum_eq (p : ℕ → ℕ) (hprime : ∀ n, 1 ≤ n → (p n).Prime)
    (hmono : ∀ m n, 1 ≤ m → m < n → p m < p n) (honto : ∀ q, q.Prime → ∃ n, 1 ≤ n ∧ p n = q)
    (n : ℕ) : p (n + 1) = Nat.nth Nat.Prime n := by
  have huniv : {n : ℕ | ∀ hf : Set.Finite (Set.ofPred Nat.Prime), n < hf.toFinset.card} = Set.univ := by
    ext n; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    intro hf; exact absurd hf primes_infinite
  have h := Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn (p := Nat.Prime) (fun m => p (m + 1))
    (by
      rw [huniv]
      intro q hq
      obtain ⟨k, hk, rfl⟩ := honto q hq
      exact ⟨k - 1, Set.mem_univ _, by show p (k - 1 + 1) = p k; congr 1; omega⟩)
    (by rw [huniv]; intro m _; exact hprime (m + 1) (by omega))
    (by rw [huniv]; intro a _ b _ hab; exact hmono (a + 1) (b + 1) (by omega) (by omega))
  exact h (by rw [huniv]; exact Set.mem_univ n)

theorem enum_eq' (p : ℕ → ℕ) (hprime : ∀ n, 1 ≤ n → (p n).Prime)
    (hmono : ∀ m n, 1 ≤ m → m < n → p m < p n) (honto : ∀ q, q.Prime → ∃ n, 1 ≤ n ∧ p n = q)
    (n : ℕ) (hn : 1 ≤ n) : p n = Problem344.primeAt n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [enum_eq p hprime hmono honto m]; simp [Problem344.primeAt]

/-- The enumeration hypotheses of readers B and C are satisfiable: `Nat.nth` shifted by one. -/
theorem nth_enum :
    let p : ℕ → ℕ := fun n => Nat.nth Nat.Prime (n - 1)
    (∀ n, 1 ≤ n → (p n).Prime) ∧ (∀ m n, 1 ≤ m → m < n → p m < p n) ∧
      ∀ q, q.Prime → ∃ n, 1 ≤ n ∧ p n = q := by
  refine ⟨fun n _ => Nat.nth_mem_of_infinite primes_infinite _, fun m n hm hmn => ?_, fun q hq => ?_⟩
  · exact Nat.nth_strictMono primes_infinite (by omega)
  · refine ⟨Nat.count Nat.Prime q + 1, by omega, ?_⟩
    simp only [Nat.add_sub_cancel]
    exact Nat.nth_count hq

theorem largeGap_eq (C : ℝ) (N : ℕ) :
    LargePrimeGaps.largeGapIndices C N = (Finset.Icc 1 N).filter
      (fun n => (Problem344.primeAt (n + 1) : ℝ) - (Problem344.primeAt n : ℝ) >
        C * Real.log (Problem344.primeAt n)) := by
  unfold LargePrimeGaps.largeGapIndices
  rfl

/-! ## From the frozen density to a positive `liminf` -/

theorem liminf_pos_of_frozen (A : Set ℕ) (h : 0 < Problem344.lowerAsymptoticDensity A)
    (f : ℕ → ℝ) (hf : ∀ N, f N = (Problem344.initialCount A N : ℝ) / N) :
    0 < liminf f atTop := by
  classical
  unfold Problem344.lowerAsymptoticDensity at h
  set S := {d : ℝ | ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → d ≤ (Problem344.initialCount A N : ℝ) / (N : ℝ)}
  have hne : S.Nonempty := by
    by_contra hS
    rw [Set.not_nonempty_iff_eq_empty] at hS
    rw [hS, Real.sSup_empty] at h; exact lt_irrefl _ h
  obtain ⟨d, ⟨N0, hd⟩, hdpos⟩ := exists_lt_of_lt_csSup hne h
  have hle1 : ∀ N, f N ≤ 1 := by
    intro N; rw [hf]
    unfold Problem344.initialCount
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · rw [div_le_one (by exact_mod_cast hN)]
      exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
  have hcob : IsCoboundedUnder (· ≥ ·) atTop f := isCoboundedUnder_ge_of_le atTop hle1
  have : d ≤ liminf f atTop := by
    refine le_liminf_of_le hcob ?_
    filter_upwards [eventually_ge_atTop N0] with N hN
    rw [hf]; exact hd N hN
  linarith

/-! ## Reader A -/

theorem pA (n : ℕ) (hn : 1 ≤ n) : ReaderA.p n = Problem344.primeAt n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp [ReaderA.p, Problem344.primeAt]

theorem gap_filter_congr (q : ℕ → ℕ) (hq : ∀ n, 1 ≤ n → q n = Problem344.primeAt n) (C : ℝ) (N : ℕ) :
    ((Finset.Icc 1 N).filter (fun n => (q (n + 1) : ℝ) - (q n : ℝ) > C * Real.log (q n))) =
      LargePrimeGaps.largeGapIndices C N := by
  rw [largeGap_eq]
  refine Finset.filter_congr fun n hn => ?_
  have h1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
  rw [hq n h1, hq (n + 1) (by omega)]

theorem thm_from_frozen (q : ℕ → ℕ) (hq : ∀ n, 1 ≤ n → q n = Problem344.primeAt n)
    (frozen : type_of% @Problem344.large_gaps_and_ratio_density) :
    ∀ C : ℝ, 0 < C → ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      c * (N : ℝ) ≤ (((Finset.Icc 1 N).filter
        (fun n => (q (n + 1) : ℝ) - (q n : ℝ) > C * Real.log (q n))).card : ℝ) := by
  intro C hC
  obtain ⟨c, hc, N₀, h⟩ := frozen.1 C hC
  exact ⟨c, hc, N₀, fun N hN => by rw [gap_filter_congr q hq]; exact h N hN⟩

/-- The readers' ratio set agrees with the frozen `ratioIncreaseIndices` on `Icc 1 N`. -/
theorem ratio_card (q : ℕ → ℕ) (hq : ∀ n, 1 ≤ n → q n = Problem344.primeAt n) (N : ℕ) :
    ((Finset.Icc 1 N).filter
      (fun n => (q n : ℝ) / (n : ℝ) < (q (n + 1) : ℝ) / ((n : ℝ) + 1))).card =
      Problem344.initialCount Problem344.ratioIncreaseIndices N := by
  classical
  unfold Problem344.initialCount
  congr 1
  refine Finset.filter_congr fun n hn => ?_
  have h1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
  rw [hq n h1, hq (n + 1) (by omega)]
  simp only [Problem344.ratioIncreaseIndices, Set.mem_setOf_eq, h1, true_and]
  push_cast; rfl

theorem cor_from_frozen (q : ℕ → ℕ) (hq : ∀ n, 1 ≤ n → q n = Problem344.primeAt n)
    (frozen : type_of% @Problem344.large_gaps_and_ratio_density) :
    0 < Filter.liminf (fun N : ℕ => ((((Finset.Icc 1 N).filter
        (fun n => (q n : ℝ) / (n : ℝ) < (q (n + 1) : ℝ) / ((n : ℝ) + 1))).card : ℕ) : ℝ) / (N : ℝ)) atTop :=
  liminf_pos_of_frozen _ frozen.2 _ fun N => by rw [ratio_card q hq]

theorem closure_A_thm (frozen : type_of% @Problem344.large_gaps_and_ratio_density) :
    type_of% @ReaderA.reading_thm_1_1 :=
  thm_from_frozen ReaderA.p pA frozen

theorem closure_A_cor (frozen : type_of% @Problem344.large_gaps_and_ratio_density) :
    type_of% @ReaderA.reading_cor_1_2 := by
  have h := cor_from_frozen ReaderA.p pA frozen
  unfold ReaderA.lowerDensity
  convert h using 2
  funext N
  simp only [ReaderA.densityRatio, ReaderA.countUpTo, ReaderA.ratioIncreaseSet, Set.mem_setOf_eq]
  congr 3
  refine Finset.filter_congr fun n hn => ?_
  simp [(Finset.mem_Icc.1 hn).1]

/-! ## Readers B and C -/

theorem closure_B_thm (frozen : type_of% @Problem344.large_gaps_and_ratio_density) :
    type_of% @ReaderB.readingTheorem11 := by
  intro p hp
  exact thm_from_frozen p (enum_eq' p hp.1 hp.2.1 hp.2.2) frozen

theorem closure_B_cor (frozen : type_of% @Problem344.large_gaps_and_ratio_density) :
    type_of% @ReaderB.readingCorollary12 := by
  intro p hp
  have h := cor_from_frozen p (enum_eq' p hp.1 hp.2.1 hp.2.2) frozen
  unfold ReaderB.lowerDensity
  convert h using 2
  funext N
  congr 3
  ext n
  simp +contextual [Finset.mem_filter, Finset.mem_Icc]

theorem closure_C_thm (frozen : type_of% @Problem344.large_gaps_and_ratio_density) :
    type_of% @ReaderC.reading_O56_thm1 := by
  intro p h1 h2 h3
  exact thm_from_frozen p (enum_eq' p h1 h2 h3) frozen

theorem closure_C_cor (frozen : type_of% @Problem344.large_gaps_and_ratio_density) :
    type_of% @ReaderC.reading_O56_cor2 := by
  intro p h1 h2 h3
  exact cor_from_frozen p (enum_eq' p h1 h2 h3) frozen

theorem reading_A_thm_closed : type_of% @ReaderA.reading_thm_1_1 :=
  closure_A_thm Problem344.large_gaps_and_ratio_density
theorem reading_A_cor_closed : type_of% @ReaderA.reading_cor_1_2 :=
  closure_A_cor Problem344.large_gaps_and_ratio_density
theorem reading_B_thm_closed : type_of% @ReaderB.readingTheorem11 :=
  closure_B_thm Problem344.large_gaps_and_ratio_density
theorem reading_B_cor_closed : type_of% @ReaderB.readingCorollary12 :=
  closure_B_cor Problem344.large_gaps_and_ratio_density
theorem reading_C_thm_closed : type_of% @ReaderC.reading_O56_thm1 :=
  closure_C_thm Problem344.large_gaps_and_ratio_density
theorem reading_C_cor_closed : type_of% @ReaderC.reading_O56_cor2 :=
  closure_C_cor Problem344.large_gaps_and_ratio_density

end TargetO.PrimeGaps

#print axioms TargetO.PrimeGaps.closure_A_thm
#print axioms TargetO.PrimeGaps.closure_A_cor
#print axioms TargetO.PrimeGaps.closure_B_thm
#print axioms TargetO.PrimeGaps.closure_B_cor
#print axioms TargetO.PrimeGaps.closure_C_thm
#print axioms TargetO.PrimeGaps.closure_C_cor
#print axioms TargetO.PrimeGaps.nth_enum
