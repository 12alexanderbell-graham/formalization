import Mathlib
import Readings.powerfree
import ComparatorChallenges.PowerFreeValues

/-! # Target O, family O57 (power-free values of polynomials): closures (run 2026-11-27T1628Z).

Frozen statement `OAI.QuarticPowerFree.allDegrees` (taken by name, never retyped): for `f` irreducible over `ℚ` with
`4 ≤ natDegree`, local admissibility at `k = natDegree − 2` gives `Multipliable` local factors, a positive
`tprod` and `count − c X = o(X)`. It is the paper's Corollary 1.2 (every `d ≥ 4`); Theorem 1.1 (`4 ≤ d ≤ 8`) is
its special case.

Links proved here:
* power-free: reader A also asks `a ≠ 0`; the frozen (and B's, C's) "no `p^k` divides `a`" already excludes `0`
  (`k`-th powers divide `0`), so the counts agree (`powerFreeA_iff`).
* `ρ`: A's is the frozen one verbatim; B and C count roots in `ZMod q`, proved equal for `q ≥ 1` (`rho_zmod`).
* Euler product: B's `HasProd` over `Nat.Primes` is the frozen `Multipliable.hasProd`; A's and C's limits of
  partial products over primes `< P` follow from the unconditional `HasProd` (`tendsto_partial`).
* hypotheses: `k + 2 = d = natDegree` gives the frozen `natDegree − 2 = k`; the readers' "no fixed prime `k`-th
  power divisor" (Corollary 1.2) implies the frozen `ρ_f(p^k) < p^k` (`admissible_of_noFixed`: if every residue
  were a root, `p^k` would divide every value). -/

namespace TargetO.PowerFree

open Filter Asymptotics Polynomial OAI.QuarticPowerFree

/-! ## `ρ` -/

theorem rho_le (f : Polynomial ℤ) (q : ℕ) : rho f q ≤ q := by
  unfold rho; exact (Finset.card_filter_le _ _).trans (by simp)

theorem rho_zmod (f : Polynomial ℤ) (q : ℕ) (hq : 0 < q) :
    Nat.card {a : ZMod q // (f.map (Int.castRingHom (ZMod q))).eval a = 0} = rho f q := by
  have : NeZero q := ⟨hq.ne'⟩
  classical
  have hev : ∀ n : ℕ, (f.map (Int.castRingHom (ZMod q))).eval (n : ZMod q) = 0 ↔ (q : ℤ) ∣ f.eval (n : ℤ) := by
    intro n
    have := eval_intCast_map (Int.castRingHom (ZMod q)) f (n : ℤ)
    rw [Int.cast_natCast] at this
    rw [this]
    simpa using ZMod.intCast_zmod_eq_zero_iff_dvd (f.eval (n : ℤ)) q
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  unfold rho
  symm
  refine Finset.card_bij' (fun n _ => (n : ZMod q)) (fun a _ => a.val) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    simpa [Finset.mem_filter] using (hev n).2 hn.2
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨ZMod.val_lt a, ?_⟩
    rw [← hev, ZMod.natCast_zmod_val]; exact ha
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    exact ZMod.val_cast_of_lt hn.1
  · intro a _
    exact ZMod.natCast_zmod_val a

/-! ## Hypotheses -/

theorem admissible_of_noFixed (f : Polynomial ℤ) (k : ℕ)
    (h : ∀ p : ℕ, p.Prime → ¬ ∀ n : ℤ, (p : ℤ) ^ k ∣ f.eval n) : LocallyAdmissible f k := by
  classical
  intro p hp
  refine lt_of_le_of_ne (rho_le f _) fun heq => h p hp fun n => ?_
  set q := p ^ k with hqdef
  have hqpos : 0 < q := pow_pos hp.pos k
  -- every residue in `range q` is a root
  have hall : (Finset.range q).filter (fun a : ℕ => (q : ℤ) ∣ f.eval (a : ℤ)) = Finset.range q := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
    unfold rho at heq; simp [heq]
  set r : ℕ := (n % (q : ℤ)).toNat
  have hr0 : 0 ≤ n % (q : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hqpos.ne')
  have hrq : n % (q : ℤ) < q := Int.emod_lt_of_pos _ (by exact_mod_cast hqpos)
  have hrr : (r : ℤ) = n % (q : ℤ) := Int.toNat_of_nonneg hr0
  have hmem : r ∈ (Finset.range q).filter (fun a : ℕ => (q : ℤ) ∣ f.eval (a : ℤ)) := by
    rw [hall, Finset.mem_range]; omega
  have hroot : (q : ℤ) ∣ f.eval (r : ℤ) := (Finset.mem_filter.1 hmem).2
  have hdiff : (q : ℤ) ∣ f.eval n - f.eval (r : ℤ) := by
    refine dvd_trans ?_ (sub_dvd_eval_sub n (r : ℤ) f)
    rw [hrr, Int.emod_def]; exact ⟨n / (q : ℤ), by ring⟩
  have := dvd_add hdiff hroot
  simp only [sub_add_cancel] at this
  have hc : ((p ^ k : ℕ) : ℤ) = (p : ℤ) ^ k := by push_cast; rfl
  rw [← hc]; exact this

theorem frozen_at (frozen : type_of% @allDegrees) (f : Polynomial ℤ) (d k : ℕ)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ))) (hdeg : f.natDegree = d) (hd4 : 4 ≤ d) (hk : k + 2 = d)
    (hloc : LocallyAdmissible f k) : DensityStatement f k := by
  have hk' : f.natDegree - 2 = k := by omega
  have := frozen f hirr (by omega) (by rw [hk']; exact hloc)
  rwa [hk'] at this

/-! ## Euler products -/

/-- The primes below `P`, as a finset of `Nat.Primes`. -/
noncomputable def primesBelow' (P : ℕ) : Finset Nat.Primes :=
  (Finset.range P).preimage ((↑) : Nat.Primes → ℕ) Nat.Primes.coe_nat_injective.injOn

theorem mem_primesBelow' (P : ℕ) (x : Nat.Primes) : x ∈ primesBelow' P ↔ (x : ℕ) < P := by
  unfold primesBelow'
  exact Finset.mem_preimage.trans Finset.mem_range

/-- From an unconditional product over the primes to the limit of partial products over primes `< P`. -/
theorem tendsto_partial (F : ℕ → ℝ) (c : ℝ) (h : HasProd (fun p : Nat.Primes => F p) c) :
    Tendsto (fun P : ℕ => ∏ p ∈ (Finset.range P).filter Nat.Prime, F p) atTop (nhds c) := by
  classical
  let s : ℕ → Finset Nat.Primes := primesBelow'
  have hs : Tendsto s atTop atTop := by
    refine Filter.tendsto_atTop_finset_of_monotone ?_ ?_
    · intro a b hab x hx
      rw [mem_primesBelow'] at hx ⊢
      exact lt_of_lt_of_le hx hab
    · intro x
      exact ⟨(x : ℕ) + 1, by rw [mem_primesBelow']; omega⟩
  have heq : ∀ P, ∏ p ∈ s P, F p = ∏ p ∈ (Finset.range P).filter Nat.Prime, F p := by
    intro P
    refine Finset.prod_bij (fun x _ => (x : ℕ)) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro x hx
      rw [mem_primesBelow'] at hx
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hx, x.2⟩
    · intro a _ b _ hab; exact Nat.Primes.coe_nat_injective hab
    · intro n hn
      obtain ⟨hn1, hn2⟩ := Finset.mem_filter.1 hn
      exact ⟨⟨n, hn2⟩, (mem_primesBelow' P _).2 (Finset.mem_range.1 hn1), rfl⟩
  have := h.comp hs
  refine this.congr fun P => ?_
  simp only [Function.comp]
  exact heq P

theorem prod_of_frozen (f : Polynomial ℤ) (k : ℕ) (h : DensityStatement f k) :
    HasProd (fun p : Nat.Primes => (1 - (rho f ((p : ℕ) ^ k) : ℝ) / ((p : ℕ) : ℝ) ^ k)) (densityConstant f k) :=
  h.1.hasProd

/-! ## Counts -/

theorem powerFreeA_iff (k : ℕ) (hk : 0 < k) (a : ℤ) : ReaderA.IsPowerFree k a ↔ PowerFree k a := by
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun h0 => h 2 Nat.prime_two (by rw [h0]; exact dvd_zero _), h⟩

theorem countA (f : Polynomial ℤ) (k : ℕ) (hk : 0 < k) (X : ℝ) : ReaderA.S f k X = count f k X := by
  classical
  unfold ReaderA.S count
  congr 1
  exact Finset.filter_congr fun n _ => powerFreeA_iff k hk _

theorem countB (f : Polynomial ℤ) (k : ℕ) (X : ℝ) : ReaderB.S f k X = count f k X := by
  classical
  unfold ReaderB.S count
  congr 1

theorem countC (f : Polynomial ℤ) (k : ℕ) (X : ℝ) : ReaderC.S f k X = (count f k X : ℝ) := by
  classical
  unfold ReaderC.S count
  congr 2

/-! ## Reader A -/

theorem rhoA (f : Polynomial ℤ) (q : ℕ) : ReaderA.rho f q = rho f q := by
  unfold ReaderA.rho rho; rfl

theorem locA (f : Polynomial ℤ) (k : ℕ) (h : ReaderA.LocallyAdmissible f k) : LocallyAdmissible f k :=
  fun p hp => by rw [← rhoA]; exact h p hp

theorem A_concl (frozen : type_of% @allDegrees) (f : Polynomial ℤ) (d k : ℕ)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ))) (hdeg : f.natDegree = d) (hd4 : 4 ≤ d) (hk : k + 2 = d)
    (hloc : LocallyAdmissible f k) :
    ∃ c : ℝ, ReaderA.IsEulerProduct f k c ∧ 0 < c ∧
      (fun X : ℝ => (ReaderA.S f k X : ℝ) - c * X) =o[atTop] (fun X : ℝ => X) := by
  have h := frozen_at frozen f d k hirr hdeg hd4 hk hloc
  refine ⟨densityConstant f k, ?_, h.2.1, ?_⟩
  · have := tendsto_partial (fun p => 1 - (rho f (p ^ k) : ℝ) / (p : ℝ) ^ k) _ (prod_of_frozen f k h)
    unfold ReaderA.IsEulerProduct ReaderA.partialEulerProduct
    refine this.congr fun P => ?_
    refine Finset.prod_congr rfl fun p _ => ?_
    simp only [ReaderA.localFactor, rhoA]
  · have h3 := h.2.2
    refine h3.congr_left fun X => ?_
    rw [countA f k (by omega) X]

theorem closure_A_thm (frozen : type_of% @allDegrees) : type_of% @ReaderA.reading_thm_1_1 := by
  intro f d k hirr hdeg hd4 _ hk hloc
  exact A_concl frozen f d k hirr hdeg hd4 hk (locA f k hloc)

theorem closure_A_cor (frozen : type_of% @allDegrees) : type_of% @ReaderA.reading_cor_1_2 := by
  intro f d k hirr hdeg hd4 hk hfix
  exact A_concl frozen f d k hirr hdeg hd4 hk (admissible_of_noFixed f k hfix)

/-! ## Reader B -/

theorem rhoB (f : Polynomial ℤ) (q : ℕ) (hq : 0 < q) : ReaderB.rho f q = rho f q := rho_zmod f q hq

theorem B_concl (frozen : type_of% @allDegrees) (f : Polynomial ℤ) (d k : ℕ)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ))) (hdeg : f.natDegree = d) (hd4 : 4 ≤ d) (hk : k + 2 = d)
    (hloc : LocallyAdmissible f k) : ReaderB.DensityStatement f k := by
  have h := frozen_at frozen f d k hirr hdeg hd4 hk hloc
  refine ⟨densityConstant f k, ?_, h.2.1, ?_⟩
  · convert prod_of_frozen f k h using 3 with p
    rw [rhoB f _ (pow_pos p.2.pos k)]
  · refine h.2.2.congr_left fun X => ?_
    rw [countB]

theorem locB (f : Polynomial ℤ) (k : ℕ) (h : ReaderB.LocallyAdmissible f k) : LocallyAdmissible f k :=
  fun p hp => by rw [← rhoB f _ (pow_pos hp.pos k)]; exact h p hp

theorem closure_B_thm (frozen : type_of% @allDegrees) : type_of% @ReaderB.readingTheorem11 := by
  intro f d k hirr hdeg hd hk hloc
  exact B_concl frozen f d k hirr hdeg hd.1 hk (locB f k hloc)

theorem closure_B_cor (frozen : type_of% @allDegrees) : type_of% @ReaderB.readingCorollary12 := by
  intro f d k hirr hdeg hd4 hk hno
  exact B_concl frozen f d k hirr hdeg hd4 hk (admissible_of_noFixed f k hno)

/-! ## Reader C -/

theorem C_concl (frozen : type_of% @allDegrees) (f : Polynomial ℤ) (d k : ℕ)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ))) (hdeg : f.natDegree = d) (hd4 : 4 ≤ d) (hk : k + 2 = d)
    (hloc : LocallyAdmissible f k) :
    ∃ c : ℝ, Tendsto (ReaderC.eulerPartial f k) atTop (nhds c) ∧ 0 < c ∧
      (fun X : ℝ => ReaderC.S f k X - c * X) =o[atTop] (fun X : ℝ => X) := by
  have h := frozen_at frozen f d k hirr hdeg hd4 hk hloc
  refine ⟨densityConstant f k, ?_, h.2.1, ?_⟩
  · have := tendsto_partial (fun p => 1 - (rho f (p ^ k) : ℝ) / (p : ℝ) ^ k) _ (prod_of_frozen f k h)
    refine this.congr fun P => ?_
    unfold ReaderC.eulerPartial
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp' : p.Prime := (Finset.mem_filter.1 hp).2
    rw [ReaderC.rho, rho_zmod f _ (pow_pos hp'.pos k)]
  · refine h.2.2.congr_left fun X => ?_
    rw [countC]

theorem closure_C_thm (frozen : type_of% @allDegrees) : type_of% @ReaderC.reading_O57_thm1 := by
  intro f hirr k d hd hk h4 _ hadm
  refine C_concl frozen f d k hirr hd h4 hk.symm fun p hp => ?_
  rw [← rho_zmod f _ (pow_pos hp.pos k)]; exact hadm p hp

theorem closure_C_cor (frozen : type_of% @allDegrees) : type_of% @ReaderC.reading_O57_cor2 := by
  intro f hirr k d hd hk h4 hno
  exact C_concl frozen f d k hirr hd h4 hk.symm (admissible_of_noFixed f k hno)

theorem reading_A_thm_closed : type_of% @ReaderA.reading_thm_1_1 := closure_A_thm allDegrees
theorem reading_A_cor_closed : type_of% @ReaderA.reading_cor_1_2 := closure_A_cor allDegrees
theorem reading_B_thm_closed : type_of% @ReaderB.readingTheorem11 := closure_B_thm allDegrees
theorem reading_B_cor_closed : type_of% @ReaderB.readingCorollary12 := closure_B_cor allDegrees
theorem reading_C_thm_closed : type_of% @ReaderC.reading_O57_thm1 := closure_C_thm allDegrees
theorem reading_C_cor_closed : type_of% @ReaderC.reading_O57_cor2 := closure_C_cor allDegrees

end TargetO.PowerFree

#print axioms TargetO.PowerFree.closure_A_thm
#print axioms TargetO.PowerFree.closure_A_cor
#print axioms TargetO.PowerFree.closure_B_thm
#print axioms TargetO.PowerFree.closure_B_cor
#print axioms TargetO.PowerFree.closure_C_thm
#print axioms TargetO.PowerFree.closure_C_cor
