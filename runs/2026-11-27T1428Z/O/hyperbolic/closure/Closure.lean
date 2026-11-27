import Mathlib
import Readings.hyperbolic
import ComparatorChallenges.TorsionFreeHyperbolic

/-! # Target O, family O52 (torsion-free hyperbolic group, not residually finite): closures (run 2026-11-27T1428Z).
Frozen statement `main` (thin triangles as walks in `SimpleGraph.mulCayley`, residual finiteness as Mathlib's
`Group.ResiduallyFinite`), taken with `type_of%`, never retyped.
* Reader A's Theorem 1.1 is closed from it: A's Cayley graph is `mulCayley`, a connected Cayley graph's set
  generates, A's function-indexed geodesics are frozen geodesic walks, and A's residual finiteness implies Mathlib's.
* Reader B's reading is false, proved here: B asks every point of a side to be near BOTH other sides; on the
  degenerate triangle (a geodesic, its reverse, a constant side) that bounds every word length, so the group is
  finite, hence (torsion-free) trivial, hence residually finite. A reading disagreement settled as a Lean fact.
* Reader C (word metric through `sInf`) is not closed here. Not linear over any field (the corollary) has no
  Lean statement; it follows by Malcev's theorem, which Mathlib lacks. -/

namespace TargetO.Hyperbolic

open OAI.Release075

/-! Reader A. -/

theorem cayley_eq {G : Type} [Group G] (S : Set G) : ReaderA.cayleyGraph S = SimpleGraph.mulCayley S := by
  ext u v
  rw [SimpleGraph.mulCayley_adj]
  rfl

theorem closure_of_connected {G : Type} [Group G] (S : Set G) (h : (SimpleGraph.mulCayley S).Connected) :
    Subgroup.closure S = ⊤ := by
  rw [eq_top_iff]
  intro g _
  obtain ⟨w⟩ := h.preconnected 1 g
  have key : ∀ (u v : G) (w : (SimpleGraph.mulCayley S).Walk u v), u ∈ Subgroup.closure S →
      v ∈ Subgroup.closure S := by
    intro u v w
    induction w with
    | nil => exact id
    | @cons a b c hab _ ih =>
      intro ha
      apply ih
      rw [SimpleGraph.mulCayley_adj] at hab
      rcases hab.2 with hs | hs
      · have : b = a * (a⁻¹ * b) := by group
        rw [this]; exact Subgroup.mul_mem _ ha (Subgroup.subset_closure hs)
      · have : b = a * (b⁻¹ * a)⁻¹ := by group
        rw [this]; exact Subgroup.mul_mem _ ha (Subgroup.inv_mem _ (Subgroup.subset_closure hs))
  exact key 1 g w (Subgroup.one_mem _)

/-- The walk through `γ 0, …, γ n`. -/
def walkOf {V : Type} (X : SimpleGraph V) (γ : ℕ → V) :
    (n : ℕ) → (∀ i < n, X.Adj (γ i) (γ (i + 1))) → X.Walk (γ 0) (γ n)
  | 0, _ => SimpleGraph.Walk.nil
  | n + 1, h => (walkOf X γ n (fun i hi => h i (by omega))).concat (h n (by omega))

theorem walkOf_length {V : Type} (X : SimpleGraph V) (γ : ℕ → V) (n : ℕ) (h : ∀ i < n, X.Adj (γ i) (γ (i + 1))) :
    (walkOf X γ n h).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [walkOf, ih]

theorem mem_support_walkOf {V : Type} (X : SimpleGraph V) (γ : ℕ → V) (n : ℕ)
    (h : ∀ i < n, X.Adj (γ i) (γ (i + 1))) (a : V) : a ∈ (walkOf X γ n h).support ↔ ∃ i ≤ n, a = γ i := by
  induction n with
  | zero =>
    simp only [walkOf, SimpleGraph.Walk.support_nil, List.mem_singleton]
    constructor
    · rintro rfl; exact ⟨0, le_refl _, rfl⟩
    · rintro ⟨i, hi, rfl⟩; rw [show i = 0 by omega]
  | succ n ih =>
    simp only [walkOf, SimpleGraph.Walk.support_concat, List.mem_append,
      List.mem_singleton, ih]
    constructor
    · rintro (⟨i, hi, rfl⟩ | rfl)
      · exact ⟨i, by omega, rfl⟩
      · exact ⟨n + 1, le_refl _, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      rcases Nat.lt_or_ge i (n + 1) with h' | h'
      · exact Or.inl ⟨i, by omega, rfl⟩
      · right; rw [show i = n + 1 by omega]

theorem geo_of_min {V : Type} {X : SimpleGraph V} {u v : V} (p : X.Walk u v)
    (h : ∀ w : X.Walk u v, p.length ≤ w.length) : Geodesic X p := by
  unfold Geodesic
  obtain ⟨w, hw⟩ := p.reachable.exists_walk_length_eq_dist
  exact le_antisymm (hw ▸ h w) (SimpleGraph.dist_le p)

theorem within_of_dist {V : Type} {X : SimpleGraph V} (hc : X.Connected) {a b : V} {δ : ℕ} (h : X.dist a b ≤ δ) :
    ReaderA.WithinDist X a b δ := by
  obtain ⟨w, hw⟩ := (hc.preconnected a b).exists_walk_length_eq_dist
  exact ⟨w, hw ▸ h⟩

theorem A_hyp {G : Type} [Group G] (h : WordHyperbolic G) : ReaderA.IsWordHyperbolic G := by
  obtain ⟨S, hS, hc, δ, hthin⟩ := h
  refine ⟨S, hS, closure_of_connected S hc, δ, ?_⟩
  rw [cayley_eq]
  intro γ₁ γ₂ γ₃ n₁ n₂ n₃ g1 g2 g3 h12 h23 h31 i hi
  set X := SimpleGraph.mulCayley S
  let p := walkOf X γ₁ n₁ g1.1
  let q := (walkOf X γ₂ n₂ g2.1).copy h12.symm rfl
  let r := (walkOf X γ₃ n₃ g3.1).copy h23.symm h31
  have gp : Geodesic X p := geo_of_min p fun w => by rw [walkOf_length]; exact g1.2 w
  have gq : Geodesic X q := geo_of_min q fun w => by
    simp only [q, SimpleGraph.Walk.length_copy, walkOf_length]
    have := g2.2 (w.copy h12 rfl)
    simpa using this
  have gr : Geodesic X r := geo_of_min r fun w => by
    simp only [r, SimpleGraph.Walk.length_copy, walkOf_length]
    have := g3.2 (w.copy h23 h31.symm)
    simpa using this
  obtain ⟨b, hb, hd⟩ := (hthin _ _ _ p q r gp gq gr).1 (γ₁ i) ((mem_support_walkOf X γ₁ n₁ g1.1 _).2 ⟨i, hi, rfl⟩)
  rcases hb with hb | hb
  · simp only [q, SimpleGraph.Walk.support_copy] at hb
    obtain ⟨j, hj, rfl⟩ := (mem_support_walkOf X γ₂ n₂ g2.1 _).1 hb
    exact ⟨j, Or.inl ⟨hj, within_of_dist hc hd⟩⟩
  · simp only [r, SimpleGraph.Walk.support_copy] at hb
    obtain ⟨j, hj, rfl⟩ := (mem_support_walkOf X γ₃ n₃ g3.1 _).1 hb
    exact ⟨j, Or.inr ⟨hj, within_of_dist hc hd⟩⟩

theorem A_thm (H : type_of% @main) : type_of% @ReaderA.readingHyperbolicMain := by
  obtain ⟨G, _, htf, hh, hrf⟩ := H
  refine ⟨G, _, fun g hg n hn hgn => hg (htf g n hn hgn), A_hyp hh, fun hA => hrf ?_⟩
  exact Group.residuallyFinite_of_forall_exists_finite_monoidHom.{0} hA

/-! Reader B's reading is false. -/

section B
variable {G : Type} [Group G] (S : Set G)

/-- A path can be extended by one generator step. -/
theorem B_extend {n : ℕ} {p : ℕ → G} (hp : ReaderB.IsPath S n p) (s : G) (hs : s ∈ S ∨ s⁻¹ ∈ S) :
    ReaderB.IsPath S (n + 1) (fun i => if i ≤ n then p i else p n * s) := by
  intro i hi
  rcases Nat.lt_or_ge i n with h | h
  · simp only [show i ≤ n by omega, show i + 1 ≤ n by omega, if_true]; exact hp i h
  · have hi' : i = n := by omega
    subst hi'
    simp only [le_refl, if_true, show ¬ (i + 1 ≤ i) by omega, if_false, inv_mul_cancel_left]
    exact hs

theorem B_reach (hgen : Subgroup.closure S = ⊤) (g : G) :
    ∃ n p, ReaderB.IsPath S n p ∧ p 0 = 1 ∧ p n = g := by
  have hg : g ∈ Subgroup.closure S := hgen ▸ Subgroup.mem_top g
  induction hg using Subgroup.closure_induction_right with
  | one => exact ⟨0, fun _ => 1, fun i hi => absurd hi (Nat.not_lt_zero _), rfl, rfl⟩
  | mul_right x _ y hy ih =>
    obtain ⟨n, p, hp, h0, hn⟩ := ih
    refine ⟨n + 1, _, B_extend S hp y (Or.inl hy), by simp [h0], by simp [hn]⟩
  | mul_inv_cancel x _ y hy ih =>
    obtain ⟨n, p, hp, h0, hn⟩ := ih
    refine ⟨n + 1, _, B_extend S hp y⁻¹ (Or.inr (by simpa using hy)), by simp [h0], by simp [hn]⟩

theorem B_rev {n : ℕ} {p : ℕ → G} (hp : ReaderB.IsPath S n p) : ReaderB.IsPath S n (fun i => p (n - i)) := by
  intro i hi
  have h := hp (n - i - 1) (by omega)
  rw [show n - i - 1 + 1 = n - i by omega] at h
  have e : (p (n - i))⁻¹ * p (n - (i + 1)) = ((p (n - i - 1))⁻¹ * p (n - i))⁻¹ := by
    rw [show n - (i + 1) = n - i - 1 by omega]; group
  rw [e, inv_inv]
  exact h.symm

/-- The endpoints of paths of length `k` from `1` form a finite set. -/
theorem B_ends_finite (hS : S.Finite) (k : ℕ) :
    {v : G | ∃ p, ReaderB.IsPath S k p ∧ p 0 = 1 ∧ p k = v}.Finite := by
  induction k with
  | zero =>
    apply (Set.finite_singleton (1 : G)).subset
    rintro v ⟨p, -, h0, hk⟩; rw [← hk, h0]; rfl
  | succ k ih =>
    apply ((ih.mul (hS.union hS.inv))).subset
    rintro v ⟨p, hp, h0, hk⟩
    refine ⟨p k, ⟨p, fun i hi => hp i (by omega), h0, rfl⟩, (p k)⁻¹ * v, ?_, by group⟩
    rcases hp k (by omega) with h | h
    · rw [← hk]; exact Or.inl h
    · rw [← hk]; exact Or.inr (by simpa using h)

theorem B_false : ¬ type_of% @ReaderB.reading_hyperbolic_main := by
  rintro ⟨G, _, htf, ⟨S, hgen, δ, hthin⟩, hnrf⟩
  apply hnrf
  -- every element is within `δ` of `1`
  have near : ∀ g : G, ∃ k ≤ δ, ∃ q, ReaderB.IsPath (S : Set G) k q ∧ q 0 = 1 ∧ q k = g := by
    intro g
    classical
    have hex := B_reach (S : Set G) hgen g
    let m := Nat.find hex
    obtain ⟨b, hb, hb0, hbm⟩ := Nat.find_spec hex
    have hgeo : ReaderB.IsGeodesic (S : Set G) m b := by
      refine ⟨hb, fun m' q hq hq0 hqm => ?_⟩
      exact Nat.find_min' hex ⟨q, hq, hq0.trans hb0, hqm.trans hbm⟩
    have hgeo' : ReaderB.IsGeodesic (S : Set G) m (fun i => b (m - i)) := by
      refine ⟨B_rev _ hb, fun m' q hq hq0 hqm => ?_⟩
      have := hgeo.2 m' (fun i => q (m' - i)) (B_rev _ hq) (by simp [hqm]) (by simp [hq0])
      exact this
    have ht := hthin m m 0 (fun i => b (m - i)) b (fun _ => g) hgeo' hgeo
      ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun m' q hq hq0 hqm => Nat.zero_le _⟩
      (by simp) hbm (by show g = b (m - 0); rw [Nat.sub_zero]; exact hbm.symm) m (le_refl _)
    obtain ⟨j, hj, k, q, hk, hq, hq0, hqk⟩ := ht.2
    refine ⟨k, hk, q, hq, ?_, by simpa using hqk⟩
    simpa [hb0] using hq0
  have hfin : (Set.univ : Set G).Finite := by
    apply (Set.finite_iUnion (fun k : Fin (δ + 1) => B_ends_finite (S : Set G) S.finite_toSet k.val)).subset
    intro g _
    obtain ⟨k, hk, q, hq, h0, hkq⟩ := near g
    exact Set.mem_iUnion.2 ⟨⟨k, by omega⟩, q, hq, h0, hkq⟩
  have : Finite G := Set.finite_univ_iff.1 hfin
  intro g hg
  exact absurd (isOfFinOrder_of_finite g) (htf g hg)

end B

end TargetO.Hyperbolic

#print axioms TargetO.Hyperbolic.A_thm
#print axioms TargetO.Hyperbolic.B_false
