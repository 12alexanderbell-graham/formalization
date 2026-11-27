import Mathlib
import Readings.UnitDist
import ComparatorChallenges.PlanarUnitDistances

/-! # Target O, family O18 (planar unit distances): closures (run 2026-11-27T0628Z).
Frozen statement taken with `type_of%`, never retyped: `∃ C β, 0 < C ∧ 1 ≤ β ∧ β < 4/3 ∧ ∀ n, u n ≤ C n^β`,
with `u n` the `sSup` of the number of unit-distance `Sym2` pairs of an `n`-point `Finset`. Each reader's
count of unit pairs (2-element subsets for A and C, `Sym2` for B) is proved equal to the frozen one, so the
maxima agree and the bound transfers; the "equivalently" big-O forms follow with δ = 4/3 − β. -/

open Filter Asymptotics

namespace TargetO.UnitDist

open OAI.PlanarUnitDistances

/-- 2-element subsets at distance 1 are counted by the frozen `Sym2` count. -/
theorem pairs_card (X : Finset Plane) :
    ((X.powersetCard 2).filter (fun s => ∃ x ∈ s, ∃ y ∈ s, dist x y = 1)).card = unitPairCount X := by
  classical
  unfold unitPairCount
  symm
  refine Finset.card_bij (fun z _ => Sym2.lift ⟨fun x y => ({x, y} : Finset Plane),
      fun x y => Finset.pair_comm x y⟩ z) ?_ ?_ ?_
  · intro z hz
    induction z using Sym2.ind with
    | h a b =>
      rw [Finset.mem_filter, Finset.mk_mem_sym2_iff] at hz
      obtain ⟨⟨ha, hb⟩, hd⟩ := hz
      have hd' : dist a b = 1 := hd
      have hne : a ≠ b := by rintro rfl; simp at hd'
      simp only [Sym2.lift_mk]
      rw [Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨?_, Finset.card_pair hne⟩, a, by simp, b, by simp, hd'⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ha
      · rw [Finset.mem_singleton.mp hx]; exact hb
  · intro z hz w hw hzw
    induction z using Sym2.ind with
    | h a b =>
    induction w using Sym2.ind with
    | h c d =>
      rw [Finset.mem_filter] at hz hw
      have hab : a ≠ b := by rintro rfl; have : dist a a = 1 := hz.2; simp at this
      have hcd : c ≠ d := by rintro rfl; have : dist c c = 1 := hw.2; simp at this
      simp only [Sym2.lift_mk] at hzw
      have ha : a ∈ ({c, d} : Finset Plane) := hzw ▸ by simp
      have hb : b ∈ ({c, d} : Finset Plane) := hzw ▸ by simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd rfl hab
      · rfl
      · exact Sym2.eq_swap
      · exact absurd rfl hab
  · intro s hs
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hs
    obtain ⟨⟨hsub, hcard⟩, x, hx, y, hy, hxy⟩ := hs
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
    have hxy' : x ≠ y := by rintro rfl; simp at hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    have hdab : dist a b = 1 := by
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact absurd rfl hxy'
      · exact hxy
      · rw [dist_comm]; exact hxy
      · exact absurd rfl hxy'
    refine ⟨s(a, b), ?_, by simp⟩
    rw [Finset.mem_filter, Finset.mk_mem_sym2_iff]
    exact ⟨⟨hsub (by simp), hsub (by simp)⟩, hdab⟩

theorem A_count (X : Finset Plane) : ReaderA.u X = unitPairCount X := by
  rw [← pairs_card]
  unfold ReaderA.u
  simp only [dist_eq_norm]

theorem C_count (X : Finset Plane) : ReaderC.UnitDist.u X = unitPairCount X := by
  rw [← pairs_card]
  unfold ReaderC.UnitDist.u ReaderC.UnitDist.unitPairs
  congr 1
  refine Finset.filter_congr fun s _ => ?_
  constructor
  · rintro ⟨x, hx, y, hy, -, h⟩; exact ⟨x, hx, y, hy, h⟩
  · rintro ⟨x, hx, y, hy, h⟩
    exact ⟨x, hx, y, hy, by rintro rfl; simp at h, h⟩

theorem B_count (X : Finset Plane) : ReaderB.u X = unitPairCount X := by
  classical
  unfold ReaderB.u unitPairCount
  rw [← Set.ncard_coe_finset]
  congr 1
  ext z
  induction z using Sym2.ind with
  | h a b =>
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mk_mem_sym2_iff]
    constructor
    · rintro ⟨x, hx, y, hy, hz, hd⟩
      rcases Sym2.eq_iff.mp hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨⟨hx, hy⟩, hd⟩
      · exact ⟨⟨hy, hx⟩, by show dist _ _ = 1; rw [dist_comm]; exact hd⟩
    · rintro ⟨⟨ha, hb⟩, hd⟩
      exact ⟨a, ha, b, hb, rfl, hd⟩

/-- Transfer a bound on the frozen maximum to a reader's maximum with the same count. -/
theorem max_eq {uR : Finset Plane → ℕ} (h : ∀ X, uR X = unitPairCount X) (n : ℕ) :
    sSup {m : ℕ | ∃ X : Finset Plane, X.card = n ∧ uR X = m} = u n := by
  unfold u
  congr 1
  ext m
  simp only [Set.mem_ofPred_eq, h]

theorem bigO_of_bound {f : ℕ → ℝ} {C β : ℝ} (hβ : β < 4 / 3) (hf : ∀ n, 0 ≤ f n)
    (hb : ∀ n : ℕ, f n ≤ C * (n : ℝ) ^ β) :
    ∃ δ : ℝ, 0 < δ ∧ f =O[atTop] (fun n : ℕ => (n : ℝ) ^ ((4 : ℝ) / 3 - δ)) := by
  refine ⟨4 / 3 - β, by linarith, ?_⟩
  have : (4 : ℝ) / 3 - (4 / 3 - β) = β := by ring
  rw [this]
  refine IsBigO.of_bound C (Eventually.of_forall fun n => ?_)
  rw [Real.norm_of_nonneg (hf n), Real.norm_of_nonneg (by positivity)]
  exact hb n

theorem A_thm : (type_of% @OAI.PlanarUnitDistances.main) → (type_of% @ReaderA.reading_thm_1_1) := by
  rintro ⟨C, β, hC, h1, h2, hb⟩
  refine ⟨C, β, hC, h1, h2, fun n => ?_⟩
  unfold ReaderA.uMax ReaderA.uValues
  rw [max_eq A_count]; exact hb n

theorem A_bigO : (type_of% @OAI.PlanarUnitDistances.main) → (type_of% @ReaderA.reading_thm_1_1_bigO) := by
  intro h
  obtain ⟨C, β, -, -, h2, hb⟩ := A_thm h
  exact bigO_of_bound h2 (fun n => Nat.cast_nonneg _) hb

theorem B_thm : (type_of% @OAI.PlanarUnitDistances.main) → (type_of% @ReaderB.reading_thm_1_1) := by
  rintro ⟨C, β, hC, h1, h2, hb⟩
  refine ⟨C, β, hC, h1, h2, fun n => ?_⟩
  unfold ReaderB.un
  rw [max_eq B_count]; exact hb n

theorem B_bigO : (type_of% @OAI.PlanarUnitDistances.main) → (type_of% @ReaderB.reading_equiv) := by
  intro h
  obtain ⟨C, β, -, -, h2, hb⟩ := B_thm h
  obtain ⟨δ, hδ, hO⟩ := bigO_of_bound h2 (fun n => Nat.cast_nonneg _) hb
  exact ⟨δ, hδ, hO⟩

theorem C_thm : (type_of% @OAI.PlanarUnitDistances.main) →
    (type_of% @ReaderC.UnitDist.reading_unitdist_bound) := by
  rintro ⟨C, β, hC, h1, h2, hb⟩
  refine ⟨C, hC, β, h1, h2, fun n => ?_⟩
  unfold ReaderC.UnitDist.uMax
  rw [max_eq C_count]; exact hb n

theorem C_bigO : (type_of% @OAI.PlanarUnitDistances.main) →
    (type_of% @ReaderC.UnitDist.reading_unitdist_bigO) := by
  intro h
  obtain ⟨C, -, β, -, h2, hb⟩ := C_thm h
  obtain ⟨δ, hδ, hO⟩ := bigO_of_bound h2 (fun n => Nat.cast_nonneg _) hb
  exact ⟨δ, hδ, hO⟩

end TargetO.UnitDist

#print axioms TargetO.UnitDist.A_thm
#print axioms TargetO.UnitDist.A_bigO
#print axioms TargetO.UnitDist.B_thm
#print axioms TargetO.UnitDist.B_bigO
#print axioms TargetO.UnitDist.C_thm
#print axioms TargetO.UnitDist.C_bigO
