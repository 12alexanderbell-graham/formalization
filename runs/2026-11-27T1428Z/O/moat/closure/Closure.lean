import Mathlib
import Readings.moat
import ComparatorChallenges.GaussianMoat

/-! # Target O, family O46 (Gaussian moat): closures (run 2026-11-27T1428Z).
Frozen statement `fullMain : MainEndpoint ∧ UniformEndpoint`, taken by name, never retyped. The frozen distance is
`dist` in `ℂ` after the coercion `ℤ[i] → ℂ`; it is proved equal to each reader's distance (A: √ of the norm;
B, C: √ of the squared coordinate differences). Closed from the frozen statement: every reader's Theorem 1.1
(component bound), every reader's "Consequently" (bounded walks) and every reader's "no infinite walk" (3/3 each).
The frozen `ncard` comes with an explicit `Finite`, so it cannot hide an infinite component. -/

namespace TargetO.Moat

open OAI.GaussianMoat

theorem distA (z w : GaussianInt) : dist (z : ℂ) (w : ℂ) = ReaderA.gdist z w := by
  unfold ReaderA.gdist
  rw [Complex.dist_eq, ← map_sub, Complex.norm_def, ← GaussianInt.intCast_real_norm]

theorem distB (z w : GaussianInt) : dist (z : ℂ) (w : ℂ) = ReaderB.gdist z w := by
  rw [distA]; unfold ReaderA.gdist ReaderB.gdist
  congr 1; simp [Zsqrtd.norm_def]; ring

theorem distC (z w : GaussianInt) : dist (z : ℂ) (w : ℂ) = ReaderC.gdist z w := distB z w

/-- The frozen component, as a set of Gaussian integers, is finite with at most `B` elements. -/
theorem comp_bound {D : ℝ} {B : ℕ} (hB : ∀ p : PrimeVertex, (component D p).Finite ∧ (component D p).ncard ≤ B)
    (p : PrimeVertex) : (component D p).encard ≤ B := by
  rw [← (hB p).1.cast_ncard_eq]; exact_mod_cast (hB p).2

/-! Theorem 1.1. -/

theorem A_graph (D : ℝ) : ∀ p q : ReaderA.GaussianPrime, (ReaderA.GD D).Adj p q ↔ (primeGraph D).Adj p q := by
  intro p q
  change (p ≠ q ∧ ReaderA.gdist p.1 q.1 ≤ D) ↔ (p ≠ q ∧ dist (p.1 : ℂ) (q.1 : ℂ) ≤ D)
  rw [distA]

theorem A_reach (D : ℝ) (p q : ReaderA.GaussianPrime) : (ReaderA.GD D).Reachable p q ↔ (primeGraph D).Reachable p q := by
  have : ReaderA.GD D = primeGraph D := SimpleGraph.ext (funext fun p => funext fun q => propext (A_graph D p q))
  rw [this]; exact Iff.rfl

theorem A_thm (H : MainEndpoint ∧ UniformEndpoint) : type_of% @ReaderA.reading_thm_1_1 := by
  intro D
  obtain ⟨B, hB, -⟩ := H.2 D
  refine ⟨B, fun c => ?_⟩
  induction c using SimpleGraph.ConnectedComponent.ind with
  | h p =>
    have e : ((ReaderA.GD D).connectedComponentMk p).supp = component D p := by
      ext q
      simp only [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq, component]
      rw [A_reach]; exact ⟨fun h => h.symm, fun h => h.symm⟩
    rw [e]; exact hB p

theorem B_thm (H : MainEndpoint ∧ UniformEndpoint) : type_of% @ReaderB.reading_moat_uniform_bound := by
  intro D
  obtain ⟨B, hB, -⟩ := H.2 D
  refine ⟨B, fun v => ?_⟩
  have e : {w : ReaderB.GPrime | (ReaderB.GD D).Reachable v w} = component D v := by
    have : ReaderB.GD D = primeGraph D := by
      ext p q
      change (p ≠ q ∧ ReaderB.gdist p.1 q.1 ≤ D) ↔ (p ≠ q ∧ dist (p.1 : ℂ) (q.1 : ℂ) ≤ D)
      rw [distB]
    rw [this]; rfl
  rw [e]; exact comp_bound hB v

theorem C_back (D : ℝ) (p q : PrimeVertex) (h : Relation.ReflTransGen (primeGraph D).Adj p q) :
    Relation.ReflTransGen (ReaderC.GD D) p.1 q.1 := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hab ih =>
    refine Relation.ReflTransGen.tail ih ⟨b.2, c.2, fun h => hab.1 (Subtype.ext h), ?_⟩
    rw [← distC]; exact hab.2

/-- Reader C's component (a set of Gaussian integers, by `ReflTransGen` of the prime-to-prime relation) is the
image of the frozen component. -/
theorem C_comp (D : ℝ) (p : PrimeVertex) : ReaderC.componentOf D p.1 = Subtype.val '' component D p := by
  ext w
  constructor
  · rintro ⟨hw, hr⟩
    refine ⟨⟨w, hw⟩, ?_, rfl⟩
    show (primeGraph D).Reachable p ⟨w, hw⟩
    rw [SimpleGraph.reachable_iff_reflTransGen]
    have key : ∀ x, Relation.ReflTransGen (ReaderC.GD D) p.1 x → ∀ hx : Irreducible x,
        Relation.ReflTransGen (primeGraph D).Adj p ⟨x, hx⟩ := by
      intro x hx
      induction hx with
      | refl => intro _; exact Relation.ReflTransGen.refl
      | tail _ hab ih =>
        intro hc
        obtain ⟨ha, -, hne, hd⟩ := hab
        refine Relation.ReflTransGen.tail (ih ha) ⟨fun h => hne (congrArg Subtype.val h), ?_⟩
        rw [distC]; exact hd
    exact key w hr hw
  · rintro ⟨q, hq, rfl⟩
    refine ⟨q.2, C_back D p q ?_⟩
    have hq' : (primeGraph D).Reachable p q := hq
    exact (SimpleGraph.reachable_iff_reflTransGen _ _).1 hq'

theorem C_thm (H : MainEndpoint ∧ UniformEndpoint) : type_of% @ReaderC.reading_moat_thm1_1 := by
  intro D
  obtain ⟨B, hB, -⟩ := H.2 D
  refine ⟨B, fun z hz => ?_⟩
  rw [show z = (⟨z, hz⟩ : PrimeVertex).1 from rfl, C_comp D ⟨z, hz⟩]
  exact (Set.encard_image_le _ _).trans (comp_bound hB _)

/-! "Consequently": bounded walks. -/

theorem A_cons (H : MainEndpoint ∧ UniformEndpoint) : type_of% @ReaderA.reading_thm_1_1_consequently := by
  intro D
  obtain ⟨B, -, hw⟩ := H.2 D
  refine ⟨B, fun n p hp hinj hd => hw n p hp hinj fun i j hij => ?_⟩
  rw [dist_comm, distA]
  have hj : i.val + 1 < n := hij ▸ j.2
  have := hd i.val hj
  have e1 : (⟨i.val, by omega⟩ : Fin n) = i := rfl
  have e2 : (⟨i.val + 1, hj⟩ : Fin n) = j := Fin.ext hij.symm
  rw [e1, e2] at this; exact this

theorem B_cons (H : MainEndpoint ∧ UniformEndpoint) : type_of% @ReaderB.reading_moat_sequences := by
  intro D
  obtain ⟨B, -, hw⟩ := H.2 D
  refine ⟨B, fun n f hf hinj hd => hw n f hf hinj fun i j hij => ?_⟩
  rw [dist_comm, distB]
  have hj : i.val + 1 < n := hij ▸ j.2
  have e2 : (⟨i.val + 1, hj⟩ : Fin n) = j := Fin.ext hij.symm
  have := hd i hj
  rw [e2] at this; exact this

theorem C_cons (H : MainEndpoint ∧ UniformEndpoint) : type_of% @ReaderC.reading_moat_consequently := by
  intro D
  obtain ⟨B, -, hw⟩ := H.2 D
  refine ⟨B, fun n p hinj hp hd => hw n p hp hinj fun i j hij => ?_⟩
  rw [dist_comm, distC]; exact hd i j hij

/-! No infinite walk. -/

theorem A_walk (H : MainEndpoint ∧ UniformEndpoint) : type_of% @ReaderA.reading_no_infinite_path := by
  rintro D ⟨f, hinj, hadj⟩
  refine H.1 D (fun t => (f t).1) (fun t => (f t).2) (fun a b h => hinj (Subtype.ext h)) fun t => ?_
  rw [dist_comm, distA]; exact (hadj t).2

theorem B_walk (H : MainEndpoint ∧ UniformEndpoint) : type_of% @ReaderB.reading_moat_no_infinite_walk := by
  rintro ⟨D, f, hf, hinj, hd⟩
  refine H.1 D f hf hinj fun t => ?_
  rw [dist_comm, distB]; exact hd t

theorem C_walk (H : MainEndpoint ∧ UniformEndpoint) : type_of% @ReaderC.reading_moat_no_infinite_path := by
  rintro D ⟨p, hinj, hp, hadj⟩
  refine H.1 D p hp hinj fun t => ?_
  rw [dist_comm, distC]; exact (hadj t).2.2.2

end TargetO.Moat

#print axioms TargetO.Moat.A_thm
#print axioms TargetO.Moat.B_thm
#print axioms TargetO.Moat.C_thm
#print axioms TargetO.Moat.A_cons
#print axioms TargetO.Moat.B_cons
#print axioms TargetO.Moat.C_cons
#print axioms TargetO.Moat.A_walk
#print axioms TargetO.Moat.B_walk
#print axioms TargetO.Moat.C_walk
