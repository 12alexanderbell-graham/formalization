import ComparatorChallenges.CycleDecomposition
import Readings.CycleDecomp

/-! Closure of the blind reading (runs/2026-11-26T1529Z/S/cycledecomp/reading.lean) against the
frozen comparator statement `OAI.ErdosGallai.erdos_gallai` (Erdős Problem 184, family 181).
Statements are taken with `type_of%`, never retyped. The frozen statement quantifies over graphs on
`Fin n`; the reading over every finite vertex type. Transport is along `Iso.comap`. -/

namespace ExternalS.CycleDecomp
open SimpleGraph

lemma transport {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W) (φ : G ≃g H) (k : ℕ)
    (hG : OAI.ErdosGallai.EdgeDecomposition G k) :
    ∃ parts : Fin k → Set (Sym2 W), CycleDecomp.IsCycleEdgeDecomposition H parts := by
  obtain ⟨parts, hcyc, hdisj, hunion⟩ := hG
  have hinj : Function.Injective (Sym2.map φ) := Sym2.map.injective φ.injective
  refine ⟨fun i => Sym2.map φ '' parts i, fun i => ?_, fun i j hij => ?_, ?_⟩
  · rcases hcyc i with ⟨v, p, hp, hs⟩ | ⟨e, he, hs⟩
    · left
      refine ⟨φ v, p.map φ.toHom, hp.map φ.injective, ?_⟩
      show (p.map φ.toHom).edgeSet = Sym2.map φ '' parts i
      rw [hs, Walk.edgeSet_map]; rfl
    · right
      refine ⟨Sym2.map φ e, (Iso.map_mem_edgeSet_iff φ).mpr he, ?_⟩
      show Sym2.map φ '' parts i = _
      rw [hs, Set.image_singleton]
  · exact (Set.disjoint_image_iff hinj).mpr (hdisj hij)
  · rw [← Set.image_iUnion, hunion]
    ext x; constructor
    · rintro ⟨y, hy, rfl⟩; exact (Iso.map_mem_edgeSet_iff φ).mpr hy
    · intro hx
      have hxx : Sym2.map φ (Sym2.map φ.symm x) = x := by
        simp [Sym2.map_map, Function.comp_def, Sym2.map_id']
      refine ⟨Sym2.map φ.symm x, ?_, hxx⟩
      rw [← Iso.map_mem_edgeSet_iff φ, hxx]; exact hx

/-- The frozen statement is equivalent to the blind reading of Theorem 1.1. -/
theorem closure :
    (type_of% @OAI.ErdosGallai.erdos_gallai) ↔ (type_of% @CycleDecomp.reading) := by
  constructor
  · rintro ⟨C, hC, h⟩
    refine ⟨C, hC, fun V _ G => ?_⟩
    let e := Fintype.equivFin V
    obtain ⟨k, hk, hkC⟩ := h (Fintype.card V) (G.comap e.symm)
    obtain ⟨parts, hparts⟩ := transport _ G (Iso.comap e.symm G) k hk
    exact ⟨k, parts, hparts, hkC⟩
  · rintro ⟨C, hC, h⟩
    refine ⟨C, hC, fun n G => ?_⟩
    obtain ⟨k, parts, ⟨hcyc, hdisj, hunion⟩, hkC⟩ := h (Fin n) G
    refine ⟨k, ⟨parts, fun i => ?_, fun i j hij => hdisj i j hij, hunion⟩, by simpa using hkC⟩
    rcases hcyc i with ⟨v, p, hp, hs⟩ | hedge
    · exact Or.inl ⟨v, p, hp, hs.symm⟩
    · exact Or.inr hedge

end ExternalS.CycleDecomp
#print axioms ExternalS.CycleDecomp.closure
