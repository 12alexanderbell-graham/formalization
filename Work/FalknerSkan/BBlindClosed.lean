import Mathlib
import Work.FalknerSkan.Bounded

/-!
# Bounded class: the blind restatement, closed (run 2026-11-08T1228Z)

The definitions `D1`, `D2`, `D3`, `IsSol`, `Bdd` and the six theorems are the blind restater's text
(Sonnet, from the claims in words only; `runs/2026-11-08T1228Z/blind/BBlind.lean`), copied verbatim
with their placeholder proofs replaced by proofs from the program's
`Work.FalknerSkan.Bounded` headlines; `toSys`, `ofSys`, `bdd_sys` (program text) convert the blind
iterated-`derivWithin` encoding (C³ on [0, ∞)) to and from the first-order system.
-/

namespace Blind.Bounded

open Set Filter Topology

/-- one-sided derivatives on [0,∞) -/
noncomputable def D1 (f : ℝ → ℝ) : ℝ → ℝ := derivWithin f (Ici 0)
noncomputable def D2 (f : ℝ → ℝ) : ℝ → ℝ := derivWithin (D1 f) (Ici 0)
noncomputable def D3 (f : ℝ → ℝ) : ℝ → ℝ := derivWithin (D2 f) (Ici 0)

/-- BVP f''' + c f f'' + 1 - (f')^2 = 0 on [0,∞), f(0)=0, f'(0)=0, f' → 1.
c = 1 Hiemenz, c = 2 Homann. -/
def IsSol (c : ℝ) (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 3 f (Ici 0) ∧
  (∀ η, 0 ≤ η → D3 f η + c * f η * D2 f η + 1 - (D1 f η)^2 = 0) ∧
  f 0 = 0 ∧ D1 f 0 = 0 ∧ Tendsto (D1 f) atTop (𝓝 1)

def Bdd (f : ℝ → ℝ) : Prop := ∀ η, 0 ≤ η → -1 ≤ D1 f η ∧ D1 f η ≤ 1


/-- From the blind `IsSol c` to the program's first-order system (program lemma, not part of the
blind text). -/
theorem toSys {c : ℝ} {f : ℝ → ℝ} (h : IsSol c f) :
    (∀ x ∈ Ici (0 : ℝ), HasDerivWithinAt f (D1 f x) (Ici 0) x) ∧
    (∀ x ∈ Ici (0 : ℝ), HasDerivWithinAt (D1 f) (D2 f x) (Ici 0) x) ∧
    (∀ x ∈ Ici (0 : ℝ), HasDerivWithinAt (D2 f)
      (-(c * f x * D2 f x) - 1 + D1 f x ^ 2) (Ici 0) x) ∧
    f 0 = 0 ∧ D1 f 0 = 0 ∧ Tendsto (D1 f) atTop (𝓝 1) := by
  obtain ⟨hc, hode, h0, h1, hlim⟩ := h
  have hu : UniqueDiffOn ℝ (Ici (0 : ℝ)) := uniqueDiffOn_Ici 0
  have c1 : ContDiffOn ℝ 2 (D1 f) (Ici 0) := hc.derivWithin hu (by norm_num)
  have c2 : ContDiffOn ℝ 1 (D2 f) (Ici 0) := c1.derivWithin hu (by norm_num)
  refine ⟨fun x hx => ((hc.differentiableOn (by norm_num)) x hx).hasDerivWithinAt,
    fun x hx => ((c1.differentiableOn (by norm_num)) x hx).hasDerivWithinAt,
    fun x hx => (((c2.differentiableOn (by norm_num)) x hx).hasDerivWithinAt).congr_deriv
      (by have := hode x hx; unfold D3 at this; linarith), h0, h1, hlim⟩

/-- From the program's first-order system to the blind `IsSol c` (program lemma). -/
theorem ofSys {c : ℝ} {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(c * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1)) :
    IsSol c f ∧ EqOn (D1 f) p (Ici 0) ∧ EqOn (D2 f) q (Ici 0) := by
  have hu : UniqueDiffOn ℝ (Ici (0 : ℝ)) := uniqueDiffOn_Ici 0
  have e1 : EqOn (D1 f) p (Ici 0) := fun x hx => (hf x hx).derivWithin (hu x hx)
  have e2 : EqOn (D2 f) q (Ici 0) := fun x hx => by
    unfold D2
    rw [derivWithin_congr e1 (e1 hx)]
    exact (hp x hx).derivWithin (hu x hx)
  have e3 : EqOn (D3 f) (fun η => -(c * f η * q η) - 1 + p η ^ 2) (Ici 0) := fun x hx => by
    unfold D3
    rw [derivWithin_congr e2 (e2 hx)]
    exact (hq x hx).derivWithin (hu x hx)
  have cf : ContinuousOn f (Ici 0) := fun x hx => (hf x hx).continuousWithinAt
  have cp : ContinuousOn p (Ici 0) := fun x hx => (hp x hx).continuousWithinAt
  have cq : ContinuousOn q (Ici 0) := fun x hx => (hq x hx).continuousWithinAt
  have k0 : ContDiffOn ℝ 0 (fun η => -(c * f η * q η) - 1 + p η ^ 2) (Ici 0) :=
    contDiffOn_zero.2 (((continuousOn_const.mul cf).mul cq).neg.sub continuousOn_const
      |>.add (cp.pow 2))
  have k1 : ContDiffOn ℝ 1 q (Ici 0) := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_derivWithin hu]
    refine ⟨fun x hx => (hq x hx).differentiableWithinAt, by simp, ?_⟩
    exact k0.congr (fun x hx => (hq x hx).derivWithin (hu x hx))
  have k2 : ContDiffOn ℝ 2 p (Ici 0) := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiffOn_succ_iff_derivWithin hu]
    refine ⟨fun x hx => (hp x hx).differentiableWithinAt, by simp, ?_⟩
    exact k1.congr (fun x hx => (hp x hx).derivWithin (hu x hx))
  have k3 : ContDiffOn ℝ 3 f (Ici 0) := by
    rw [show (3 : WithTop ℕ∞) = 2 + 1 from rfl, contDiffOn_succ_iff_derivWithin hu]
    refine ⟨fun x hx => (hf x hx).differentiableWithinAt, by simp, ?_⟩
    exact k2.congr (fun x hx => (hf x hx).derivWithin (hu x hx))
  have hlimD : Tendsto (D1 f) atTop (𝓝 1) := by
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact (e1 (Set.mem_Ici.2 hx)).symm
  refine ⟨⟨k3, fun η hη => ?_, hf0, by rw [e1 (Set.mem_Ici.2 le_rfl)]; exact hp0, hlimD⟩, e1, e2⟩
  have hm : η ∈ Ici (0 : ℝ) := hη
  rw [e3 hm, e2 hm, e1 hm]; ring

theorem bdd_sys {f : ℝ → ℝ} (hb : Bdd f) : ∀ η ∈ Ici (0 : ℝ), -1 ≤ D1 f η ∧ D1 f η ≤ 1 :=
  fun η hη => hb η hη

-- Hiemenz
theorem hiemenz_W (f : ℝ → ℝ) (h : IsSol 1 f) (hb : Bdd f) :
    1.2325876568 < D2 f 0 ∧ D2 f 0 < 1.2325876569 := by
  obtain ⟨A, B, C, E0, E1, L⟩ := toSys h
  exact Work.FalknerSkan.Bounded.hiemenz_bounded_window _ _ _ A B
    (fun x hx => (C x hx).congr_deriv (by ring)) E0 E1 L (bdd_sys hb)

theorem hiemenz_U (f g : ℝ → ℝ) (hf : IsSol 1 f) (hg : IsSol 1 g)
    (hfb : Bdd f) (hgb : Bdd g) : EqOn f g (Ici 0) := by
  obtain ⟨A, B, C, E0, E1, L⟩ := toSys hf
  obtain ⟨A', B', C', E0', E1', L'⟩ := toSys hg
  exact fun x hx => (Work.FalknerSkan.Bounded.hiemenz_bounded_equal _ _ _ _ _ _ A B
    (fun x hx => (C x hx).congr_deriv (by ring)) E0 E1 L (bdd_sys hfb) A' B'
    (fun x hx => (C' x hx).congr_deriv (by ring)) E0' E1' L' (bdd_sys hgb) x hx).1

theorem hiemenz_E : ∃ f : ℝ → ℝ, IsSol 1 f ∧ (∀ η, 0 ≤ η → 0 ≤ D1 f η ∧ D1 f η < 1) ∧
    1.2325876568 < D2 f 0 ∧ D2 f 0 < 1.2325876569 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, hb, hlo, hhi⟩ :=
    Work.FalknerSkan.Bounded.hiemenz_exists_bounded
  obtain ⟨hs, e1, e2⟩ := ofSys (c := 1) hf hp
    (fun x hx => (hq x hx).congr_deriv (by ring)) hf0 hp0 hlim
  refine ⟨f, hs, fun η hη => ?_, ?_, ?_⟩
  · rw [e1 (Set.mem_Ici.2 hη)]; exact hb η hη
  · rw [e2 (Set.mem_Ici.2 le_rfl)]; exact hlo
  · rw [e2 (Set.mem_Ici.2 le_rfl)]; exact hhi

-- Homann
theorem homann_W (f : ℝ → ℝ) (h : IsSol 2 f) (hb : Bdd f) :
    1.3119376938 < D2 f 0 ∧ D2 f 0 < 1.3119376939 := by
  obtain ⟨A, B, C, E0, E1, L⟩ := toSys h
  exact Work.FalknerSkan.Bounded.homann_bounded_window _ _ _ A B C E0 E1 L (bdd_sys hb)

theorem homann_U (f g : ℝ → ℝ) (hf : IsSol 2 f) (hg : IsSol 2 g)
    (hfb : Bdd f) (hgb : Bdd g) : EqOn f g (Ici 0) := by
  obtain ⟨A, B, C, E0, E1, L⟩ := toSys hf
  obtain ⟨A', B', C', E0', E1', L'⟩ := toSys hg
  exact fun x hx => (Work.FalknerSkan.Bounded.homann_bounded_equal _ _ _ _ _ _ A B C E0 E1 L
    (bdd_sys hfb) A' B' C' E0' E1' L' (bdd_sys hgb) x hx).1

theorem homann_E : ∃ f : ℝ → ℝ, IsSol 2 f ∧ (∀ η, 0 ≤ η → 0 ≤ D1 f η ∧ D1 f η < 1) ∧
    1.3119376938 < D2 f 0 ∧ D2 f 0 < 1.3119376939 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, hb, hlo, hhi⟩ :=
    Work.FalknerSkan.Bounded.homann_exists_bounded
  obtain ⟨hs, e1, e2⟩ := ofSys (c := 2) hf hp hq hf0 hp0 hlim
  refine ⟨f, hs, fun η hη => ?_, ?_, ?_⟩
  · rw [e1 (Set.mem_Ici.2 hη)]; exact hb η hη
  · rw [e2 (Set.mem_Ici.2 le_rfl)]; exact hlo
  · rw [e2 (Set.mem_Ici.2 le_rfl)]; exact hhi

end Blind.Bounded
