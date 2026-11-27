import Mathlib
import Readings.LatticeCov
import ComparatorChallenges.SingleLatticeCovering

/-! # Target O, family O25 (a single lattice covering of density O(n log n)): closures (run 2026-11-27T0628Z).
Frozen statement taken with `type_of%`, never retyped: some C > 0 such that for n ≥ 2 and every convex body
K ⊆ (Fin n → ℝ) a discrete `IsZLattice` ℤ-submodule L has K + L = univ and (vol K).toReal / covolume L ≤
C n log n. Closed (frozen ⇒ reading), every reader: A and C describe the lattice by n generating vectors (A as
the columns of an invertible matrix, C as a linearly independent family): a ℤ-basis of L (rank n) gives them,
with L = their ℤ-span and covolume L = |det| (`ZLattice.covolume_eq_det`); B works in `EuclideanSpace`, where the
lattice is L pulled back along the volume-preserving `EuclideanSpace.equiv` (`ZLattice.covolume_comap`). -/

open MeasureTheory Module Matrix
open scoped Pointwise

namespace TargetO.LatticeCov

variable {n : ℕ}

/-- A ℤ-basis of a full lattice in `Fin n → ℝ`, indexed by `Fin n`. -/
theorem basis_fin (L : Submodule ℤ (Fin n → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L] :
    Nonempty (Basis (Fin n) ℤ L) := by
  have h : Module.finrank ℤ L = n := by
    rw [ZLattice.rank ℝ L, Module.finrank_fin_fun]
  exact ⟨Module.finBasisOfFinrankEq ℤ L h⟩

/-- The lattice is the set of integer combinations of a basis. -/
theorem mem_iff (L : Submodule ℤ (Fin n → ℝ)) (b : Basis (Fin n) ℤ L) (x : Fin n → ℝ) :
    x ∈ L ↔ ∃ z : Fin n → ℤ, x = ∑ j, z j • (b j : Fin n → ℝ) := by
  constructor
  · intro hx
    refine ⟨b.repr ⟨x, hx⟩, ?_⟩
    have := congrArg (fun y : L => (y : Fin n → ℝ)) (b.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    exact this.symm
  · rintro ⟨z, rfl⟩
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (b j).2

theorem C_thm : (type_of% @OAI.SingleLatticeCovering.single_lattice_covering) →
    (type_of% @ReaderC.reading_latticecov_main) := by
  intro h
  obtain ⟨C, hC, hK⟩ := h
  refine ⟨C, hC, fun n hn K hKb => ?_⟩
  obtain ⟨L, hd, hz, hcov, hb⟩ := hK n hn K hKb
  obtain ⟨b⟩ := basis_fin L
  let b' : Fin n → (Fin n → ℝ) := fun i => (b i : Fin n → ℝ)
  have hset : ((ReaderC.latticeOf b' : AddSubgroup (Fin n → ℝ)) : Set (Fin n → ℝ)) = (L : Set _) := by
    ext x
    constructor
    · intro hx
      have hle : ReaderC.latticeOf b' ≤ L.toAddSubgroup := by
        unfold ReaderC.latticeOf
        rw [AddSubgroup.closure_le]
        rintro _ ⟨i, rfl⟩
        exact (b i).2
      exact hle hx
    · intro hx
      obtain ⟨z, rfl⟩ := (mem_iff L b x).mp hx
      show _ ∈ ReaderC.latticeOf b'
      refine AddSubgroup.sum_mem _ fun j _ => AddSubgroup.zsmul_mem _ ?_ _
      exact AddSubgroup.subset_closure (Set.mem_range_self j)
  refine ⟨b', ?_, ?_, ?_⟩
  · have := (b.ofZLatticeBasis ℝ L).linearIndependent
    convert this using 1
    funext i
    exact (b.ofZLatticeBasis_apply ℝ L i).symm
  · rw [hset]; exact hcov
  · unfold ReaderC.covol
    have hd' : ZLattice.covolume L = |(Matrix.of b').det| := ZLattice.covolume_eq_det L b
    rw [← hd']
    exact hb

theorem A_thm : (type_of% @OAI.SingleLatticeCovering.single_lattice_covering) →
    (type_of% @ReaderA.reading_thm_1_1) := by
  intro h
  obtain ⟨C, hC, hK⟩ := h
  refine ⟨C, hC, fun n hn K hKb => ?_⟩
  obtain ⟨hconv, hcomp, hint⟩ := hKb
  obtain ⟨L, hd, hz, hcov, hb⟩ := hK n hn K ⟨hcomp, hconv, hint⟩
  obtain ⟨b⟩ := basis_fin L
  let M : Matrix (Fin n) (Fin n) ℝ := (Matrix.of fun i => (b i : Fin n → ℝ))ᵀ
  have hdet : ZLattice.covolume L = |M.det| := by
    rw [Matrix.det_transpose]; exact ZLattice.covolume_eq_det L b
  have hpos : 0 < |M.det| := hdet ▸ ZLattice.covolume_pos L volume
  have hmul : ∀ v : Fin n → ℤ, M.mulVec (fun i => (v i : ℝ)) = ∑ j, v j • (b j : Fin n → ℝ) := by
    intro v
    funext i
    simp only [M, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply, Finset.sum_apply,
      Pi.smul_apply, zsmul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hset : ReaderA.latticeOf M = (L : Set (Fin n → ℝ)) := by
    ext x
    simp only [ReaderA.latticeOf, Set.mem_range, SetLike.mem_coe, mem_iff L b x, hmul]
    exact ⟨fun ⟨z, hz⟩ => ⟨z, hz.symm⟩, fun ⟨z, hz⟩ => ⟨z, hz.symm⟩⟩
  refine ⟨M, fun h0 => by simp [h0] at hpos, by rw [hset]; exact hcov, ?_⟩
  rw [← ENNReal.ofReal_toReal (hcomp.measure_lt_top (μ := volume)).ne]
  apply ENNReal.ofReal_le_ofReal
  rw [hdet, div_le_iff₀ hpos] at hb
  exact hb

theorem B_thm : (type_of% @OAI.SingleLatticeCovering.single_lattice_covering) →
    (type_of% @ReaderB.reading_latticecov_main) := by
  intro h
  obtain ⟨C, hC, hK⟩ := h
  refine ⟨C, hC, fun n hn K hKb => ?_⟩
  obtain ⟨hconv, hcomp, hint⟩ := hKb
  let e := EuclideanSpace.equiv (Fin n) ℝ
  set K' : Set (Fin n → ℝ) := e '' K
  have hc' : IsCompact K' := hcomp.image e.continuous
  have hconv' : Convex ℝ K' := hconv.linear_image e.toLinearEquiv.toLinearMap
  have hint' : (interior K').Nonempty := by
    obtain ⟨x, hx⟩ := hint
    refine ⟨e x, ?_⟩
    rw [show K' = e.toHomeomorph '' K from rfl, ← e.toHomeomorph.image_interior]
    exact ⟨x, hx, rfl⟩
  obtain ⟨L, hd, hz, hcov, hb⟩ := hK n hn K' ⟨hc', hconv', hint'⟩
  have hmp : MeasurePreserving e volume volume :=
    EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)
  refine ⟨ZLattice.comap ℝ L e.toLinearMap, inferInstance, inferInstance, ?_, ?_⟩
  · ext y
    simp only [Set.mem_univ, iff_true]
    have hy : e y ∈ K' + (L : Set (Fin n → ℝ)) := by
      unfold OAI.SingleLatticeCovering.LatticeCovers at hcov
      rw [hcov]; exact Set.mem_univ _
    obtain ⟨_, ⟨k, hk, rfl⟩, l, hl, hsum⟩ := hy
    refine ⟨k, hk, e.symm l, ?_, ?_⟩
    · show e.symm l ∈ ((ZLattice.comap ℝ L e.toLinearMap : Submodule ℤ _) : Set (EuclideanSpace ℝ (Fin n)))
      rw [ZLattice.coe_comap]
      show e.toLinearMap (e.symm l) ∈ (L : Set (Fin n → ℝ))
      simpa using hl
    · apply e.injective
      rw [map_add, ContinuousLinearEquiv.apply_symm_apply]
      exact hsum
  · have hvol : volume K = volume K' := by
      rw [show K = e ⁻¹' K' from (Set.preimage_image_eq K e.injective).symm]
      exact (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)).measure_preimage_equiv K'
    rw [hvol, ZLattice.covolume_comap L volume volume hmp]
    exact hb

end TargetO.LatticeCov

#print axioms TargetO.LatticeCov.A_thm
#print axioms TargetO.LatticeCov.B_thm
#print axioms TargetO.LatticeCov.C_thm
