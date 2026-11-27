import Mathlib
import Readings.thintree
import ComparatorChallenges.StrongThinTree

/-! # Target O, family O63 (strong thin trees): closures (run 2026-11-27T1628Z).

Frozen statement `OAI.StrongThinTree.strongThinTree : MainStatement` (taken by name, never retyped): one `C > 0`
such that every loopless multigraph on `Fin n` (`n ≥ 2`) with edges `Fin m` (endpoint maps `left`, `right`) that is
`k`-edge-connected (`k ≥ 1`) has a spanning tree `T`, meaning `T` meets every nonempty proper cut and no edge of
`T` can be removed with that property kept, with `|δ_T(S)| ≤ (C / k) |δ_G(S)|` for every nonempty proper `S`.

The readers' multigraphs are arbitrary finite types `V`, `E` with `ends : E → Sym2 V`, loopless. The closure:
* transports a reader's multigraph to the frozen one on `Fin (card V)`, `Fin (card E)` (`Fintype.equivFin`, a
  representative of each `Sym2`), and the cuts both ways (`cut_card`: the frozen cut of the image of `S` has the
  reader's cut size);
* proves, on the reader's side, that the frozen spanning-tree property (cut-connected and cut-minimal) makes the
  simple graph of the tree's endpoint pairs connected (`gconn`) and minimally connected (`gmin`), hence a tree
  (Mathlib's `isTree_of_minimal_connected`), with no two parallel tree edges (`ginj`), hence `|T| + 1 = |V|`.
Reader A's spanning tree (no parallel edges, the simple graph is a tree) and readers B's and C's (the simple graph is
connected and `|T| + 1 = |V|`) both follow. -/

namespace TargetO.ThinTree

open OAI.StrongThinTree

/-! ## Generic graph facts on the readers' side -/

section Generic

variable {V E : Type} (ends : E → Sym2 V)

/-- An edge crosses `S`: one endpoint in `S`, one outside. -/
def Cr (S : Set V) (e : E) : Prop := (∃ v ∈ ends e, v ∈ S) ∧ (∃ w ∈ ends e, w ∉ S)

/-- The simple graph of the endpoint pairs of `T`. -/
def H (T : Set E) : SimpleGraph V := SimpleGraph.fromEdgeSet (ends '' T)

variable {ends}

theorem reach_mem {G' : SimpleGraph V} {S : Set V} (hS : ∀ a b, G'.Adj a b → (a ∈ S ↔ b ∈ S)) {a b : V}
    (h : G'.Reachable a b) : (a ∈ S ↔ b ∈ S) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (hS _ _ hadj).trans ih

theorem cr_of_mem (hl : ∀ e, ¬ (ends e).IsDiag) {S : Set V} {e : E} {u v : V} (he : ends e = s(u, v))
    (hu : u ∈ S) (hv : v ∉ S) : Cr ends S e :=
  ⟨⟨u, by rw [he]; exact Sym2.mem_mk_left u v, hu⟩, ⟨v, by rw [he]; exact Sym2.mem_mk_right u v, hv⟩⟩

theorem gconn [Nonempty V] (hl : ∀ e, ¬ (ends e).IsDiag) (T : Set E)
    (hconn : ∀ S : Set V, S.Nonempty → S ≠ Set.univ → ∃ e ∈ T, Cr ends S e) : (H ends T).Connected := by
  obtain ⟨v0⟩ := ‹Nonempty V›
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨v0, ?_⟩
  by_contra hne
  push_neg at hne
  set S : Set V := {v | (H ends T).Reachable v0 v}
  have hSne : S.Nonempty := ⟨v0, SimpleGraph.Reachable.refl _⟩
  have hSu : S ≠ Set.univ := by
    obtain ⟨w, hw⟩ := hne
    intro h; exact hw (h ▸ Set.mem_univ w : w ∈ S)
  obtain ⟨e, heT, ⟨v, hv, hvS⟩, ⟨w, hw, hwS⟩⟩ := hconn S hSne hSu
  have hvw : v ≠ w := fun h => hwS (h ▸ hvS)
  have hends : ends e = s(v, w) := (Sym2.mem_and_mem_iff hvw).1 ⟨hv, hw⟩
  have hadj : (H ends T).Adj v w := by
    rw [H, SimpleGraph.fromEdgeSet_adj]
    exact ⟨⟨e, heT, hends⟩, hvw⟩
  exact hwS (SimpleGraph.Reachable.trans hvS hadj.reachable)

/-- The frozen minimality, read on the reader's side. -/
def MinCut (T : Set E) : Prop :=
  ∀ e ∈ T, ∃ S : Set V, S.Nonempty ∧ S ≠ Set.univ ∧ ∀ e' ∈ T, e' ≠ e → ¬ Cr ends S e'

theorem cr_unique {T : Set E} (hconn : ∀ S : Set V, S.Nonempty → S ≠ Set.univ → ∃ e ∈ T, Cr ends S e)
    {e : E} {S : Set V} (hS1 : S.Nonempty) (hS2 : S ≠ Set.univ) (hS : ∀ e' ∈ T, e' ≠ e → ¬ Cr ends S e') :
    Cr ends S e := by
  obtain ⟨e'', he'', hcr⟩ := hconn S hS1 hS2
  by_cases h : e'' = e
  · exact h ▸ hcr
  · exact absurd hcr (hS e'' he'' h)

theorem ginj {T : Set E} (hconn : ∀ S : Set V, S.Nonempty → S ≠ Set.univ → ∃ e ∈ T, Cr ends S e)
    (hmin : MinCut (ends := ends) T) : Set.InjOn ends T := by
  intro e he e' he' heq
  by_contra hne
  obtain ⟨S, hS1, hS2, hS⟩ := hmin e he
  have hcr := cr_unique hconn hS1 hS2 hS
  exact hS e' he' (Ne.symm hne) (by unfold Cr at hcr ⊢; rw [← heq]; exact hcr)

theorem gmin [Nonempty V] (hl : ∀ e, ¬ (ends e).IsDiag) (T : Set E)
    (hconn : ∀ S : Set V, S.Nonempty → S ≠ Set.univ → ∃ e ∈ T, Cr ends S e)
    (hmin : MinCut (ends := ends) T) : Minimal SimpleGraph.Connected (H ends T) := by
  refine ⟨gconn hl T hconn, fun G' hG' hle u v huv => ?_⟩
  by_contra hnot
  rw [H, SimpleGraph.fromEdgeSet_adj] at huv
  obtain ⟨⟨e, heT, hends⟩, huv'⟩ := huv
  obtain ⟨S, hS1, hS2, hS⟩ := hmin e heT
  have hcr := cr_unique hconn hS1 hS2 hS
  -- every edge of G' stays on one side of S
  have hside : ∀ a b, G'.Adj a b → (a ∈ S ↔ b ∈ S) := by
    intro a b hab
    have hab' := hle hab
    rw [H, SimpleGraph.fromEdgeSet_adj] at hab'
    obtain ⟨⟨e', he'T, hends'⟩, hne'⟩ := hab'
    by_cases hee : e' = e
    · subst hee
      rw [hends] at hends'
      rcases Sym2.eq_iff.1 hends' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd hab hnot
      · exact absurd hab.symm hnot
    · have := hS e' he'T hee
      constructor
      · intro ha; by_contra hb; exact this (cr_of_mem hl hends' ha hb)
      · intro hb; by_contra ha; exact this (cr_of_mem hl (by rw [hends', Sym2.eq_swap]) hb ha)
  have hr := reach_mem hside (hG'.preconnected u v)
  obtain ⟨⟨x, hx, hxS⟩, ⟨y, hy, hyS⟩⟩ := hcr
  rw [hends] at hx hy
  rcases Sym2.mem_iff.1 hx with rfl | rfl <;> rcases Sym2.mem_iff.1 hy with rfl | rfl
  · exact hyS hxS
  · exact hyS (hr.1 hxS)
  · exact hyS (hr.2 hxS)
  · exact hyS hxS

theorem gtree [Nonempty V] (hl : ∀ e, ¬ (ends e).IsDiag) (T : Set E)
    (hconn : ∀ S : Set V, S.Nonempty → S ≠ Set.univ → ∃ e ∈ T, Cr ends S e)
    (hmin : MinCut (ends := ends) T) : (H ends T).IsTree :=
  SimpleGraph.isTree_of_minimal_connected (gmin hl T hconn hmin)

theorem gcard [Fintype V] [Fintype E] [Nonempty V] (hl : ∀ e, ¬ (ends e).IsDiag) (T : Set E)
    (hconn : ∀ S : Set V, S.Nonempty → S ≠ Set.univ → ∃ e ∈ T, Cr ends S e)
    (hmin : MinCut (ends := ends) T) : T.ncard + 1 = Fintype.card V := by
  classical
  have ht := gtree hl T hconn hmin
  have hc := ht.card_edgeFinset
  rw [← hc, SimpleGraph.edgeFinset, ← Set.ncard_eq_toFinset_card']
  congr 1
  rw [H, SimpleGraph.edgeSet_fromEdgeSet]
  have : ends '' T \ Sym2.diagSet = ends '' T := by
    ext z; constructor
    · exact fun h => h.1
    · rintro ⟨e, he, rfl⟩; exact ⟨⟨e, he, rfl⟩, fun h => hl e (Sym2.mem_diagSet.1 h)⟩
  rw [this, (ginj hconn hmin).ncard_image]

end Generic

/-! ## Transport to the frozen multigraph -/

section Transport

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] (ends : E → Sym2 V)

noncomputable def eV : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
noncomputable def eE : E ≃ Fin (Fintype.card E) := Fintype.equivFin E

/-- The two endpoints chosen for an edge. -/
noncomputable def pr (e : E) : V × V := Quot.out (ends e)

theorem pr_spec (e : E) : ends e = s((pr ends e).1, (pr ends e).2) := (Quot.out_eq (ends e)).symm

/-- The reader's multigraph as the frozen one. -/
noncomputable def toFrozen (hl : ∀ e, ¬ (ends e).IsDiag) : MultiGraph (Fintype.card V) (Fintype.card E) where
  left i := eV (pr ends ((eE).symm i)).1
  right i := eV (pr ends ((eE).symm i)).2
  loopless i h := by
    apply hl ((eE).symm i)
    rw [pr_spec ends ((eE).symm i), (eV).injective h]
    exact Sym2.mk_isDiag_iff.2 rfl

/-- A set of vertices as a frozen `Finset`, and back. -/
noncomputable def φ (S : Set V) : Finset (Fin (Fintype.card V)) := by
  classical exact Finset.univ.filter fun i => (eV).symm i ∈ S

def ψ (S : Finset (Fin (Fintype.card V))) : Set V := {v | eV v ∈ S}

theorem ψφ (S : Set V) : ψ (φ S) = S := by
  ext v; simp [ψ, φ]

theorem φψ (S : Finset (Fin (Fintype.card V))) : φ (ψ S) = S := by
  ext i; simp [ψ, φ]

theorem φ_nonempty (S : Set V) : (φ S).Nonempty ↔ S.Nonempty := by
  constructor
  · rintro ⟨i, hi⟩; simp [φ] at hi; exact ⟨_, hi⟩
  · rintro ⟨v, hv⟩; exact ⟨eV v, by simp [φ, hv]⟩

theorem φ_univ (S : Set V) : φ S = Finset.univ ↔ S = Set.univ := by
  constructor
  · intro h; rw [← ψφ S, h]; ext v; simp [ψ]
  · rintro rfl; ext i; simp [φ]

theorem cr_iff (hl : ∀ e, ¬ (ends e).IsDiag) (S : Set V) (e : E) :
    Cr ends S e ↔ (((toFrozen ends hl).left (eE e) ∈ φ S ∧ (toFrozen ends hl).right (eE e) ∉ φ S) ∨
      ((toFrozen ends hl).right (eE e) ∈ φ S ∧ (toFrozen ends hl).left (eE e) ∉ φ S)) := by
  simp only [toFrozen, Equiv.symm_apply_apply, φ, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold Cr
  rw [pr_spec ends e]
  simp only [Sym2.mem_iff, exists_eq_or_imp, exists_eq_left]
  tauto

/-- The frozen cut of `φ S` inside a frozen edge set `F` corresponding to `T` has the reader's cut size. -/
theorem cut_card (hl : ∀ e, ¬ (ends e).IsDiag) (F : Finset (Fin (Fintype.card E))) (T : Set E)
    (hF : ∀ i, i ∈ F ↔ (eE (E := E)).symm i ∈ T) (S : Set V) :
    ((toFrozen ends hl).cut F (φ S)).card = {e | e ∈ T ∧ Cr ends S e}.ncard := by
  have hset : (((toFrozen ends hl).cut F (φ S) : Finset _) : Set (Fin (Fintype.card E))) =
      eE '' {e | e ∈ T ∧ Cr ends S e} := by
    ext i
    simp only [MultiGraph.cut, Finset.coe_filter, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hT, hc⟩
      refine ⟨(eE).symm i, ⟨(hF i).1 hT, (cr_iff ends hl S _).2 (by simpa using hc)⟩, by simp⟩
    · rintro ⟨e, ⟨hT, hc⟩, rfl⟩
      exact ⟨(hF _).2 (by simpa using hT), by simpa using (cr_iff ends hl S e).1 hc⟩
  rw [← Set.ncard_coe_finset, hset, Set.ncard_image_of_injective _ (eE (E := E)).injective]

theorem card_V2 (h : 2 ≤ Fintype.card V) : Nonempty V := Fintype.card_pos_iff.1 (by omega)

open Classical in
/-- The core: from the frozen theorem, every reader-side multigraph has a tree with the frozen properties. -/
theorem core (frozen : MainStatement) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (V E : Type) [Fintype V] [Fintype E] (ends : E → Sym2 V),
      (∀ e, ¬ (ends e).IsDiag) → 2 ≤ Fintype.card V →
      (∀ S : Set V, S.Nonempty → S ≠ Set.univ → k ≤ {e | Cr ends S e}.ncard) →
      ∃ T : Set E, (∀ S : Set V, S.Nonempty → S ≠ Set.univ → ∃ e ∈ T, Cr ends S e) ∧ MinCut (ends := ends) T ∧
        ∀ S : Set V, S.Nonempty → S ≠ Set.univ →
          ({e | e ∈ T ∧ Cr ends S e}.ncard : ℝ) ≤ C / k * ({e | Cr ends S e}.ncard : ℝ) := by
  classical
  obtain ⟨C, hC, h⟩ := frozen
  refine ⟨C, hC, fun k hk V E _ _ ends hl hV hconn => ?_⟩
  have huniv : ∀ S : Set V, {e | Cr ends S e} = {e | e ∈ (Set.univ : Set E) ∧ Cr ends S e} := by
    intro S; ext e; simp
  have hU : ∀ i, i ∈ (Finset.univ : Finset (Fin (Fintype.card E))) ↔ (eE (E := E)).symm i ∈ (Set.univ : Set E) :=
    fun i => by simp
  obtain ⟨T, ⟨hTc, hTm⟩, hTb⟩ := h k hk _ _ hV (toFrozen ends hl) (by
    intro S hS1 hS2
    have := hconn (ψ S) (by rw [← φ_nonempty, φψ]; exact hS1) (by rw [Ne, ← φ_univ, φψ]; exact hS2)
    rw [huniv, ← cut_card ends hl _ _ hU, φψ] at this
    exact this)
  set T' : Set E := {e | eE e ∈ T}
  have hT : ∀ i, i ∈ T ↔ (eE (E := E)).symm i ∈ T' := fun i => by simp [T']
  refine ⟨T', fun S hS1 hS2 => ?_, fun e he => ?_, fun S hS1 hS2 => ?_⟩
  · have := hTc (φ S) ((φ_nonempty S).2 hS1) (fun h => hS2 ((φ_univ S).1 h))
    rw [← Finset.card_pos, cut_card ends hl _ _ hT] at this
    obtain ⟨e, he, hc⟩ := Set.nonempty_of_ncard_ne_zero this.ne'
    exact ⟨e, he, hc⟩
  · have hnc := hTm (eE e) he
    simp only [MultiGraph.Connected, not_forall] at hnc
    obtain ⟨S, hS1, hS2, hS⟩ := hnc
    refine ⟨ψ S, by rw [← φ_nonempty, φψ]; exact hS1, by rw [Ne, ← φ_univ, φψ]; exact hS2,
      fun e' he' hne hc => hS ?_⟩
    have hTe : ∀ i, i ∈ T.erase (eE e) ↔ (eE (E := E)).symm i ∈ T' \ {e} := by
      intro i
      simp only [Finset.mem_erase, Set.mem_diff, Set.mem_singleton_iff, T', Set.mem_setOf_eq,
        Equiv.apply_symm_apply]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h2, fun h => h1 (by rw [← h]; simp)⟩
      · rintro ⟨h2, h1⟩; exact ⟨fun h => h1 (by rw [h]; simp), h2⟩
    rw [← φψ S, ← Finset.card_pos, cut_card ends hl _ _ hTe]
    exact (Set.ncard_pos (Set.toFinite _)).2 ⟨e', ⟨⟨he', hne⟩, hc⟩⟩
  · have := hTb (φ S) ((φ_nonempty S).2 hS1) (fun h => hS2 ((φ_univ S).1 h))
    rw [cut_card ends hl _ _ hT, cut_card ends hl _ _ hU, ← huniv] at this
    exact this

end Transport

/-! ## The three readers -/

theorem crA_iff {V E : Type} [Fintype V] [Fintype E] (G : ReaderA.Multigraph V E) (S : Set V) (e : E) :
    ReaderA.Crosses G S e ↔ Cr G.ends S e := by
  constructor
  · rintro ⟨u, hu, w, hw, he⟩; exact cr_of_mem G.loopless he hu hw
  · rintro ⟨⟨v, hv, hvS⟩, ⟨w, hw, hwS⟩⟩
    have hvw : v ≠ w := fun h => hwS (h ▸ hvS)
    exact ⟨v, hvS, w, hwS, (Sym2.mem_and_mem_iff hvw).1 ⟨hv, hw⟩⟩

theorem closure_A (frozen : type_of% @strongThinTree) : type_of% @ReaderA.reading_thm_1_1 := by
  classical
  obtain ⟨C, hC, h⟩ := core frozen
  refine ⟨C, hC, fun k hk V E _ _ G hV hk' => ?_⟩
  have hne := card_V2 hV
  have hcut : ∀ (F : Set E) S, ReaderA.cut G F S = {e | e ∈ F ∧ Cr G.ends S e} := by
    intro F S; ext e; simp [ReaderA.cut, crA_iff]
  obtain ⟨T, hc, hm, hb⟩ := h k hk V E G.ends G.loopless hV (by
    intro S h1 h2; have := hk' S ⟨h1, h2⟩; rw [hcut] at this; simpa using this)
  refine ⟨T, ⟨ginj hc hm, gtree G.loopless T hc hm⟩, fun S ⟨h1, h2⟩ => ?_⟩
  rw [hcut, hcut]
  have := hb S h1 h2
  simpa using this

theorem closure_B (frozen : type_of% @strongThinTree) : type_of% @ReaderB.readingThinTree := by
  classical
  obtain ⟨C, hC, h⟩ := core frozen
  refine ⟨C, hC, fun k hk V E _ _ G hV hk' => ?_⟩
  have hne := card_V2 hV
  have hcut : ∀ (F : Set E) S, G.cut F S = {e | e ∈ F ∧ Cr G.ends S e} := fun F S => rfl
  obtain ⟨T, hc, hm, hb⟩ := h k hk V E G.ends G.loopless hV (by
    intro S h1 h2; have := hk' S h1 h2; rw [hcut] at this; simpa using this)
  refine ⟨T, ⟨gconn G.loopless T hc, gcard G.loopless T hc hm⟩, fun S h1 h2 => ?_⟩
  rw [hcut, hcut]
  have := hb S h1 h2
  simpa using this

theorem closure_C (frozen : type_of% @strongThinTree) : type_of% @ReaderC.reading_thm_1_1 := by
  classical
  obtain ⟨C, hC, h⟩ := core frozen
  refine ⟨C, hC, fun V E _ _ ends hl k hk hV hk' => ?_⟩
  have hne := card_V2 hV
  have hsz : ∀ (F : Set E) (S : Finset V), ReaderC.cutSize ends S F = {e | e ∈ F ∧ Cr ends (S : Set V) e}.ncard :=
    fun F S => rfl
  obtain ⟨T, hc, hm, hb⟩ := h k hk V E ends hl hV (by
    intro S h1 h2
    have hS := hk' (Set.toFinset S) (by simpa using h1) (by
      intro h; apply h2; ext v; simpa using Finset.ext_iff.1 h v)
    rw [hsz] at hS; simpa using hS)
  refine ⟨T, ⟨gconn hl T hc, gcard hl T hc hm⟩, fun S h1 h2 => ?_⟩
  rw [hsz, hsz]
  have := hb (S : Set V) (by simpa using h1) (by
    intro h; apply h2; ext v; simpa using Set.ext_iff.1 h v)
  simpa using this

theorem reading_A_closed : type_of% @ReaderA.reading_thm_1_1 := closure_A strongThinTree
theorem reading_B_closed : type_of% @ReaderB.readingThinTree := closure_B strongThinTree
theorem reading_C_closed : type_of% @ReaderC.reading_thm_1_1 := closure_C strongThinTree

end TargetO.ThinTree

#print axioms TargetO.ThinTree.closure_A
#print axioms TargetO.ThinTree.closure_B
#print axioms TargetO.ThinTree.closure_C
