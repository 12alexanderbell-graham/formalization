import Mathlib
import Readings.Mahler
import ComparatorChallenges.MahlerConjecture

/-! # Target O, family O20 (the symmetric Mahler conjecture): closures (run 2026-11-27T0628Z).
Frozen statement taken with `type_of%`, never retyped: for n ≥ 1 and K ⊆ (Fin n → ℝ) compact, convex,
symmetric (∀ x ∈ K, −x ∈ K) with nonempty interior, 4ⁿ/n! ≤ (vol K).toReal · (vol K°).toReal, with
K° = {p | ∀ v ∈ K, ∑ pᵢ vᵢ ≤ 1}. Closed (frozen ⇒ reading): every reader's inequality. Reader A works in
`Fin n → ℝ` (its polar is the frozen one up to the order of each product; its `−K = K` gives the frozen
symmetry); readers B and C work in `EuclideanSpace ℝ (Fin n)`, carried to `Fin n → ℝ` by the volume-preserving
`EuclideanSpace.equiv`, under which their inner-product polar is the frozen coordinate polar. The frozen real
inequality gives the readers' `ℝ≥0∞` one since `ofReal (a.toReal) ≤ a`. Not closed: every reader's equality
case (linear Hanner bodies): the release has no Lean statement of it. -/

open MeasureTheory

namespace TargetO.Mahler

open OAI.SymmetricMahler

/-- From the frozen real inequality to an `ℝ≥0∞` one. -/
theorem ennreal_of {n : ℕ} {a b : ENNReal} (h : (4 : ℝ) ^ n / (n.factorial : ℝ) ≤ a.toReal * b.toReal) :
    ENNReal.ofReal ((4 : ℝ) ^ n / (n.factorial : ℝ)) ≤ a * b := by
  calc ENNReal.ofReal ((4 : ℝ) ^ n / (n.factorial : ℝ)) ≤ ENNReal.ofReal (a.toReal * b.toReal) :=
        ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal a.toReal * ENNReal.ofReal b.toReal := ENNReal.ofReal_mul ENNReal.toReal_nonneg
    _ ≤ a * b := mul_le_mul' ENNReal.ofReal_toReal_le ENNReal.ofReal_toReal_le

theorem const_eq (n : ℕ) :
    (4 : ENNReal) ^ n / (n.factorial : ENNReal) = ENNReal.ofReal ((4 : ℝ) ^ n / (n.factorial : ℝ)) := by
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast Nat.factorial_pos n), ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_natCast]
  norm_num

theorem A_ineq : (type_of% @OAI.SymmetricMahler.symmetric_mahler) →
    (type_of% @ReaderA.reading_mahler_inequality) := by
  intro h n hn K hK hsymm
  obtain ⟨hc, hconv, hint⟩ := hK
  have hs : ∀ x ∈ K, -x ∈ K := fun x hx => by
    rw [← hsymm]; exact Set.neg_mem_neg.mpr hx
  have hpol : ReaderA.polarBody K = coordinatePolar K := by
    ext y
    simp only [ReaderA.polarBody, ReaderA.dotR, coordinatePolar, Set.mem_setOf_eq]
    refine forall₂_congr fun x _ => ?_
    rw [Finset.sum_congr rfl fun i _ => mul_comm (x i) (y i)]
  rw [const_eq, hpol]
  exact ennreal_of (h hn hc hconv hs hint)

/-- The Euclidean transfer used for readers B and C. -/
theorem euclid {n : ℕ} (hn : 1 ≤ n) (h : type_of% @OAI.SymmetricMahler.symmetric_mahler)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hs : ∀ x ∈ K, -x ∈ K) (hint : (interior K).Nonempty) :
    ENNReal.ofReal ((4 : ℝ) ^ n / (n.factorial : ℝ)) ≤
      volume K * volume {y : EuclideanSpace ℝ (Fin n) | ∀ x ∈ K, inner ℝ x y ≤ 1} := by
  set L := EuclideanSpace.equiv (Fin n) ℝ
  set K' : Set (Fin n → ℝ) := L '' K
  have hc' : IsCompact K' := hc.image L.continuous
  have hconv' : Convex ℝ K' := hconv.linear_image L.toLinearEquiv.toLinearMap
  have hs' : ∀ x ∈ K', -x ∈ K' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨-x, hs x hx, map_neg L x⟩
  have hint' : (interior K').Nonempty := by
    obtain ⟨x, hx⟩ := hint
    refine ⟨L x, ?_⟩
    rw [show K' = L.toHomeomorph '' K from rfl, ← L.toHomeomorph.image_interior]
    exact ⟨x, hx, rfl⟩
  have hvol : ∀ S : Set (Fin n → ℝ), volume (L ⁻¹' S) = volume S := fun S =>
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)).measure_preimage_equiv S
  have hK : K = L ⁻¹' K' := (Set.preimage_image_eq K L.injective).symm
  have hpol : {y : EuclideanSpace ℝ (Fin n) | ∀ x ∈ K, inner ℝ x y ≤ 1} = L ⁻¹' coordinatePolar K' := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_preimage, coordinatePolar, K', Set.forall_mem_image]
    refine forall₂_congr fun x _ => ?_
    rw [PiLp.inner_apply]
    simp only [RCLike.inner_apply, conj_trivial]
    rfl
  rw [hpol, hvol, hK, hvol]
  exact ennreal_of (h hn hc' hconv' hs' hint')

theorem B_ineq : (type_of% @OAI.SymmetricMahler.symmetric_mahler) →
    (type_of% @ReaderB.readingMahlerInequality) := by
  intro h n hn K hK hsymm
  obtain ⟨hc, hconv, hint⟩ := hK
  exact euclid hn h K hc hconv hsymm hint

theorem C_ineq : (type_of% @OAI.SymmetricMahler.symmetric_mahler) →
    (type_of% @ReaderC.readingC_mahler_inequality) := by
  intro h n hn K hK hsymm
  obtain ⟨hc, hconv, hint⟩ := hK
  exact euclid hn h K hc hconv (fun x hx => (hsymm x).mp hx) hint

end TargetO.Mahler

#print axioms TargetO.Mahler.A_ineq
#print axioms TargetO.Mahler.B_ineq
#print axioms TargetO.Mahler.C_ineq
