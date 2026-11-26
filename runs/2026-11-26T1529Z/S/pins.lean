import ComparatorChallenges.ShortEgyptianFractions
import ComparatorChallenges.CycleDecomposition
import ComparatorChallenges.QuantitativeVanDerWaerden

/-! Definition pins for the three frozen target-S statements: each frozen definition evaluated on a
small case whose value is known by hand, so a shifted index, a junk value or a wrong encoding would
fail here. -/

namespace ExternalS.Pins

section Egyptian
open OAI.ShortEgyptian

lemma key (l : List ℕ) : (List.map (fun n : ℚ => 1 / n) (do let a ← l; pure (a:ℚ))) =
    l.map (fun n : ℕ => 1 / (n:ℚ)) := by
  induction l with
  | nil => rfl
  | cons x t ih => simp only [List.map_cons] at *; rw [← ih]; rfl

/-- `N(2,3) = 2`: `2/3 = 1/2 + 1/6`, and `2/3` is not a unit fraction. -/
theorem minLength_two_three : minLength 2 3 = 2 := by
  have hmem : 2 ∈ {k : ℕ | ∃ ns : List ℕ, IsExpansion 2 3 ns ∧ ns.length = k} := by
    refine ⟨[2, 6], ⟨by decide, by decide, ?_⟩, rfl⟩
    rw [key]; norm_num
  apply le_antisymm (Nat.sInf_le hmem)
  apply le_csInf ⟨2, hmem⟩
  rintro k ⟨ns, ⟨hp, h2, hs⟩, rfl⟩
  rw [key] at hs
  match ns, hs, h2 with
  | [], hs, _ => norm_num at hs
  | [n], hs, h2 =>
    exfalso
    have hn : (2 : ℕ) ≤ n := h2 n (by simp)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hs
    have hn0 : (n : ℚ) ≠ 0 := by positivity
    field_simp at hs
    have h' : (3 : ℕ) = n * 2 := by exact_mod_cast hs
    omega
  | _ :: _ :: _, _, _ => simp

end Egyptian

section CycleDecomp
open OAI.ErdosGallai SimpleGraph

/-- The triangle is one cycle: `K₃` has an edge decomposition with one part. -/
theorem triangle_one : EdgeDecomposition (⊤ : SimpleGraph (Fin 3)) 1 := by
  let p : (⊤ : SimpleGraph (Fin 3)).Walk 0 0 :=
    Walk.cons (by decide : (⊤ : SimpleGraph (Fin 3)).Adj 0 1)
      (Walk.cons (by decide : (⊤ : SimpleGraph (Fin 3)).Adj 1 2)
        (Walk.cons (by decide : (⊤ : SimpleGraph (Fin 3)).Adj 2 0) Walk.nil))
  have hp : p.IsCycle := by
    rw [Walk.isCycle_def]; refine ⟨⟨by decide⟩, by simp [p], by decide⟩
  refine ⟨fun _ => p.edgeSet, fun _ => Or.inl ⟨0, p, hp, rfl⟩, fun i j hij => ?_, ?_⟩
  · exact absurd (Subsingleton.elim i j) hij
  · ext e
    induction e using Sym2.ind with
    | _ x y =>
      simp only [Set.iUnion_const, Walk.mem_edgeSet, edgeSet_top, p]
      revert x y; decide

/-- …and it has no decomposition with zero parts (zero parts cover no edge). -/
theorem triangle_not_zero : ¬ EdgeDecomposition (⊤ : SimpleGraph (Fin 3)) 0 := by
  rintro ⟨parts, -, -, hU⟩
  have : s(0, 1) ∈ (⊤ : SimpleGraph (Fin 3)).edgeSet := by simp
  rw [← hU] at this
  obtain ⟨i, -⟩ := Set.mem_iUnion.mp this
  exact i.elim0

end CycleDecomp

section Vdw
open OAI.QuantitativeVanDerWaerden

lemma ramsey_two_three : IsRamsey (Fin 2) 2 3 := by
  intro c
  by_cases h01 : c 0 = c 1
  · exact ⟨0, 1, by norm_num, by norm_num, fun j hj => by interval_cases j <;> simp [h01]⟩
  by_cases h12 : c 1 = c 2
  · exact ⟨1, 1, by norm_num, by norm_num, fun j hj => by interval_cases j <;> simp [h12]⟩
  have h02 : c 0 = c 2 := by
    have a := (c 0).isLt; have b := (c 1).isLt; have d := (c 2).isLt
    rw [Fin.ext_iff] at h01 h12 ⊢; omega
  exact ⟨0, 2, by norm_num, by norm_num, fun j hj => by interval_cases j <;> simp [h02]⟩

lemma not_ramsey_two_two : ¬ IsRamsey (Fin 2) 2 2 := by
  intro h
  obtain ⟨a, d, hd, hlt, hm⟩ := h (fun x => if x = 0 then 0 else 1)
  have := hm 1 (by norm_num)
  have ha : a = 0 := by omega
  have hd1 : d = 1 := by omega
  subst ha hd1; simp at this

lemma not_ramsey_one (k : ℕ) (hk : 2 ≤ k) : ¬ IsRamsey (Fin 2) k 1 := by
  intro h
  obtain ⟨a, d, hd, hlt, -⟩ := h (fun _ => 0)
  have : 1 ≤ (k - 1) * d := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  omega

/-- `W₂(2) = 3`: pins the interval `{0,…,N-1}`, the strict bound, and `d > 0`. -/
theorem W_two_two : W 2 2 = 3 := by
  have hmem : 3 ∈ {N : ℕ | 0 < N ∧ IsRamsey (Fin 2) 2 N} := ⟨by norm_num, ramsey_two_three⟩
  apply le_antisymm (Nat.sInf_le hmem)
  apply le_csInf ⟨3, hmem⟩
  rintro m ⟨hm, hR⟩
  by_contra hlt
  interval_cases m
  · exact not_ramsey_one 2 le_rfl hR
  · exact not_ramsey_two_two hR

end Vdw
end ExternalS.Pins

#print axioms ExternalS.Pins.minLength_two_three
#print axioms ExternalS.Pins.triangle_one
#print axioms ExternalS.Pins.triangle_not_zero
#print axioms ExternalS.Pins.W_two_two
