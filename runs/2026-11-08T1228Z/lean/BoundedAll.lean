import Mathlib
import Work.FalknerSkan.MonotoneWindow
import Work.FalknerSkan.MonotoneExists

/-!
# Scratch (run 2026-11-08T1228Z, auditor role while run 1028Z holds the LOCK)

From the class "f'' > 0 on [0, ∞)" to the class "−1 < f' < 1 on [0, ∞)" (Coppel's class
0 ≤ f' < 1 is inside it). For f''' + k f f'' + 1 − f'² = 0 written as f' = p, p' = q,
q' = −k f q − 1 + p², any solution with p → 1 and |p| < 1 on [0, ∞) has q > 0 on [0, ∞).

Argument: at a zero of q the equation gives q' = −1 + p² < 0, so q can only cross zero
downwards (fencing theorem with the barrier 0). If q(η₀) ≤ 0 for some η₀ ≥ 0, then q ≤ 0 on
[η₀, ∞), p is non-increasing there, p ≤ p(η₀) < 1, and p cannot tend to 1. Neither k nor the
boundary values f(0), p(0) are used.
-/

namespace Scratch1228
open Set Filter Topology

/-- q has a right derivative on [0, ∞) whose value is negative wherever q vanishes: once
q ≤ 0, it stays ≤ 0. -/
theorem stays_nonpos {q q' : ℝ → ℝ}
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (q' η) (Ici 0) η)
    (hz : ∀ η ∈ Ici (0 : ℝ), q η = 0 → q' η < 0)
    {η₀ : ℝ} (h0 : 0 ≤ η₀) (hle : q η₀ ≤ 0) : ∀ η, η₀ ≤ η → q η ≤ 0 := by
  intro η hη
  have hcont : ContinuousOn q (Icc η₀ η) := fun x hx =>
    ((hq x (h0.trans hx.1)).continuousWithinAt).mono (fun y hy => h0.trans hy.1)
  have hder : ∀ x ∈ Ico η₀ η, HasDerivWithinAt q (q' x) (Ici x) x := fun x hx =>
    (hq x (h0.trans hx.1)).mono (fun y hy => h0.trans (hx.1.trans hy))
  have := image_le_of_deriv_right_lt_deriv_boundary' (B := fun _ => (0 : ℝ))
    (B' := fun _ => (0 : ℝ)) hcont hder hle continuousOn_const
    (fun x _ => hasDerivWithinAt_const _ _ _)
    (fun x hx hqx => hz x (h0.trans hx.1) hqx)
  exact this ⟨hη, le_rfl⟩

/-- p has right derivative q ≤ 0 on [η₀, ∞): p is not larger than p(η₀) there. -/
theorem le_start {p q : ℝ → ℝ}
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    {η₀ : ℝ} (h0 : 0 ≤ η₀) (hneg : ∀ η, η₀ ≤ η → q η ≤ 0) :
    ∀ η, η₀ ≤ η → p η ≤ p η₀ := by
  intro η hη
  have hcont : ContinuousOn p (Icc η₀ η) := fun x hx =>
    ((hp x (h0.trans hx.1)).continuousWithinAt).mono (fun y hy => h0.trans hy.1)
  have hder : ∀ x ∈ Ico η₀ η, HasDerivWithinAt p (q x) (Ici x) x := fun x hx =>
    (hp x (h0.trans hx.1)).mono (fun y hy => h0.trans (hx.1.trans hy))
  have := image_le_of_deriv_right_le_deriv_boundary (B := fun _ => p η₀)
    (B' := fun _ => (0 : ℝ)) hcont hder le_rfl continuousOn_const
    (fun x _ => hasDerivWithinAt_const _ _ _) (fun x hx => hneg x hx.1)
  exact this ⟨hη, le_rfl⟩

/-- Falkner–Skan-type system f' = p, p' = q, q' = −k f q − 1 + p² (any real k): a solution with
p → 1 and −1 < p < 1 on [0, ∞) has q > 0 on [0, ∞). -/
theorem pos_of_abs_lt_one {k : ℝ} {f p q : ℝ → ℝ}
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(k * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hlim : Tendsto p atTop (𝓝 1))
    (hb : ∀ η ∈ Ici (0 : ℝ), -1 < p η ∧ p η < 1) :
    ∀ η ∈ Ici (0 : ℝ), 0 < q η := by
  intro η₀ hη₀
  have h0 : (0 : ℝ) ≤ η₀ := hη₀
  by_contra hcon
  have hle : q η₀ ≤ 0 := not_lt.1 hcon
  have hz : ∀ η ∈ Ici (0 : ℝ), q η = 0 → -(k * f η * q η) - 1 + p η ^ 2 < 0 := by
    intro η hη hqη
    obtain ⟨h1, h2⟩ := hb η hη
    rw [hqη]
    nlinarith
  have hneg := stays_nonpos hq hz h0 hle
  have hpl := le_start hp h0 hneg
  have hlt1 : p η₀ < 1 := (hb η₀ hη₀).2
  have hev : ∀ᶠ η in atTop, p η₀ < p η :=
    hlim.eventually (lt_mem_nhds hlt1)
  obtain ⟨η, hη⟩ := (hev.and (eventually_ge_atTop η₀)).exists
  exact absurd (hpl η hη.2) (not_le.2 hη.1)

end Scratch1228

/-!
# Scratch (run 2026-11-08T1228Z): uniqueness tools for f''' + k f f'' + 1 − f'² = 0

* `uniq_right`, `uniq_left`: forward / backward uniqueness for an autonomous field that is
  locally Lipschitz (Lipschitz on the compact union of the two trajectories' images).
* `eq_of_start`: two solutions on [0, ∞) with the same (f, f', f'') at 0 agree on [0, ∞).
* `abs_lt_of_abs_le`: a solution with f'(0) = 0 and −1 ≤ f' ≤ 1 on [0, ∞) has −1 < f' < 1
  (a touch of ±1 at η₁ > 0 is an interior extremum of f', so f''(η₁) = 0, and backward
  uniqueness against the straight line f' ≡ ±1 forces f'(0) = ±1).
-/

namespace Scratch1228
open Set Filter Topology

/-- The first-order field (f, p, q) ↦ (p, q, −k f q − 1 + p²). -/
def fsV (k : ℝ) (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (x.2.1, x.2.2, -(k * x.1 * x.2.2) - 1 + x.2.1 ^ 2)

theorem fsV_lip (k : ℝ) : LocallyLipschitz (fsV k) := by
  have : ContDiff ℝ 1 (fsV k) := by unfold fsV; fun_prop
  exact this.locallyLipschitz

theorem uniq_right {v : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ} (hv : LocallyLipschitz v) {a b : ℝ}
    {Y Z : ℝ → ℝ × ℝ × ℝ}
    (hY : ContinuousOn Y (Icc a b)) (hY' : ∀ t ∈ Ico a b, HasDerivWithinAt Y (v (Y t)) (Ici t) t)
    (hZ : ContinuousOn Z (Icc a b)) (hZ' : ∀ t ∈ Ico a b, HasDerivWithinAt Z (v (Z t)) (Ici t) t)
    (h : Y a = Z a) : EqOn Y Z (Icc a b) := by
  set S := Y '' Icc a b ∪ Z '' Icc a b
  have hS : IsCompact S :=
    (isCompact_Icc.image_of_continuousOn hY).union (isCompact_Icc.image_of_continuousOn hZ)
  obtain ⟨K, hK⟩ :=
    ((locallyLipschitzOn_univ.2 hv).mono (subset_univ S)).exists_lipschitzOnWith_of_compact hS
  exact ODE_solution_unique_of_mem_Icc_right (v := fun _ => v) (s := fun _ => S) (K := K)
    (fun _ _ => hK) hY hY' (fun t ht => Or.inl ⟨t, Ico_subset_Icc_self ht, rfl⟩) hZ hZ'
    (fun t ht => Or.inr ⟨t, Ico_subset_Icc_self ht, rfl⟩) h

theorem uniq_left {v : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ} (hv : LocallyLipschitz v) {a b : ℝ}
    {Y Z : ℝ → ℝ × ℝ × ℝ}
    (hY : ContinuousOn Y (Icc a b)) (hY' : ∀ t ∈ Ioc a b, HasDerivWithinAt Y (v (Y t)) (Iic t) t)
    (hZ : ContinuousOn Z (Icc a b)) (hZ' : ∀ t ∈ Ioc a b, HasDerivWithinAt Z (v (Z t)) (Iic t) t)
    (h : Y b = Z b) : EqOn Y Z (Icc a b) := by
  set S := Y '' Icc a b ∪ Z '' Icc a b
  have hS : IsCompact S :=
    (isCompact_Icc.image_of_continuousOn hY).union (isCompact_Icc.image_of_continuousOn hZ)
  obtain ⟨K, hK⟩ :=
    ((locallyLipschitzOn_univ.2 hv).mono (subset_univ S)).exists_lipschitzOnWith_of_compact hS
  exact ODE_solution_unique_of_mem_Icc_left (v := fun _ => v) (s := fun _ => S) (K := K)
    (fun _ _ => hK) hY hY' (fun t ht => Or.inl ⟨t, Ioc_subset_Icc_self ht, rfl⟩) hZ hZ'
    (fun t ht => Or.inr ⟨t, Ioc_subset_Icc_self ht, rfl⟩) h

/-- The three scalar derivatives assemble into one for the triple. -/
theorem triple {k : ℝ} {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(k * f η * q η) - 1 + p η ^ 2) (Ici 0) η) :
    ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun t => (f t, p t, q t))
      (fsV k (f η, p η, q η)) (Ici 0) η :=
  fun η hη => (hf η hη).prodMk ((hp η hη).prodMk (hq η hη))

theorem triple_cont {k : ℝ} {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(k * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (b : ℝ) : ContinuousOn (fun t => (f t, p t, q t)) (Icc 0 b) := fun x hx =>
  ((triple hf hp hq x hx.1).continuousWithinAt).mono (fun _ hy => hy.1)

/-- Two solutions on [0, ∞) with the same values of f, f', f'' at 0 agree on [0, ∞). -/
theorem eq_of_start {k : ℝ} {f p q f₂ p₂ q₂ : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(k * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hf₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η)
    (hp₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η)
    (hq₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(k * f₂ η * q₂ η) - 1 + p₂ η ^ 2) (Ici 0) η)
    (h0 : f 0 = f₂ 0) (h1 : p 0 = p₂ 0) (h2 : q 0 = q₂ 0) :
    ∀ η ∈ Ici (0 : ℝ), f η = f₂ η ∧ p η = p₂ η ∧ q η = q₂ η := by
  intro η hη
  have hη0 : (0 : ℝ) ≤ η := hη
  have key := uniq_right (fsV_lip k) (triple_cont hf hp hq η) (fun t ht =>
      (triple hf hp hq t ht.1).mono (fun y hy => ht.1.trans hy))
    (triple_cont hf₂ hp₂ hq₂ η) (fun t ht =>
      (triple hf₂ hp₂ hq₂ t ht.1).mono (fun y hy => ht.1.trans hy))
    (by simp only [h0, h1, h2]) ⟨hη0, le_rfl⟩
  simp only [Prod.mk.injEq] at key
  exact key

/-- If f' = ±1 at some η₁ ≥ 0 while −1 ≤ f' ≤ 1 on [0, ∞), then f'(0) = ±1. -/
theorem start_of_touch {k s : ℝ} (hs : s = 1 ∨ s = -1) {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(k * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hb : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1)
    {η₁ : ℝ} (hη₁ : 0 < η₁) (htouch : p η₁ = s) : p 0 = s := by
  have hnhds : ∀ t, 0 < t → Ici (0 : ℝ) ∈ 𝓝 t := fun t ht => Ici_mem_nhds ht
  have hpd : HasDerivAt p (q η₁) η₁ := (hp η₁ hη₁.le).hasDerivAt (hnhds η₁ hη₁)
  have hq1 : q η₁ = 0 := by
    rcases hs with rfl | rfl
    · have hmax : IsLocalMax p η₁ := by
        filter_upwards [hnhds η₁ hη₁] with y hy
        rw [htouch]; exact (hb y hy).2
      exact hmax.hasDerivAt_eq_zero hpd
    · have hmin : IsLocalMin p η₁ := by
        filter_upwards [hnhds η₁ hη₁] with y hy
        rw [htouch]; exact (hb y hy).1
      exact hmin.hasDerivAt_eq_zero hpd
  have hs2 : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
  set Z : ℝ → ℝ × ℝ × ℝ := fun t => (f η₁ + s * (t - η₁), s, 0) with hZ
  have hZd : ∀ t, HasDerivAt Z (fsV k (Z t)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => f η₁ + s * (t - η₁)) s t := by
      simpa using ((hasDerivAt_id t).sub_const η₁).const_mul s |>.const_add (f η₁)
    have := h1.prodMk ((hasDerivAt_const t s).prodMk (hasDerivAt_const t (0 : ℝ)))
    convert this using 1
    simp only [fsV, hZ, mul_zero, neg_zero, zero_sub, hs2]
    norm_num
  have key := uniq_left (fsV_lip k) (a := 0) (b := η₁) (triple_cont hf hp hq η₁)
    (fun t ht => ((triple hf hp hq t ht.1.le).hasDerivAt (hnhds t ht.1)).hasDerivWithinAt)
    (fun t _ => (hZd t).continuousAt.continuousWithinAt)
    (fun t _ => (hZd t).hasDerivWithinAt)
    (by simp only [hZ, sub_self, mul_zero, add_zero, htouch, hq1]) ⟨le_rfl, hη₁.le⟩
  simp only [hZ, Prod.mk.injEq] at key
  exact key.2.1

/-- A solution with f'(0) = 0 and −1 ≤ f' ≤ 1 on [0, ∞) has −1 < f' < 1 on [0, ∞). -/
theorem abs_lt_of_abs_le {k : ℝ} {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(k * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hp0 : p 0 = 0) (hb : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) :
    ∀ η ∈ Ici (0 : ℝ), -1 < p η ∧ p η < 1 := by
  intro η hη
  have hη0 : (0 : ℝ) ≤ η := hη
  obtain ⟨h1, h2⟩ := hb η hη
  rcases eq_or_lt_of_le hη0 with h | hpos
  · subst h; rw [hp0]; norm_num
  refine ⟨lt_of_le_of_ne h1 (fun he => ?_), lt_of_le_of_ne h2 (fun he => ?_)⟩
  · have := start_of_touch (Or.inr rfl) hf hp hq hb hpos he.symm
    rw [hp0] at this; norm_num at this
  · have := start_of_touch (Or.inl rfl) hf hp hq hb hpos he
    rw [hp0] at this; norm_num at this

end Scratch1228

/-! ## Candidate headlines (to be frozen when the LOCK is free) -/

namespace Scratch1228
open Set Filter Topology

/-- From −1 ≤ p ≤ 1 (and p(0) = 0, p → 1): q > 0 on [0, ∞). -/
theorem pos_of_abs_le {k : ℝ} {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(k * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hb : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) : ∀ η ∈ Ici (0 : ℝ), 0 < q η :=
  pos_of_abs_lt_one hp hq hlim (abs_lt_of_abs_le hf hp hq hp0 hb)

/-- Hiemenz stagnation-point flow: every solution of f''' + f f'' + 1 − f'² = 0 on [0, ∞)
(f has derivative p, p has derivative q, q has derivative −f q − 1 + p², one-sided at 0) with
f(0) = 0, p(0) = 0, p(η) → 1 as η → ∞ and −1 ≤ p ≤ 1 on [0, ∞) has wall shear q(0) = f''(0)
strictly between 1.2325876568 and 1.2325876569. -/
theorem hiemenz_bounded_window (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hb : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) :
    1.2325876568 < q 0 ∧ q 0 < 1.2325876569 := by
  have hq1 : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(1 * f η * q η) - 1 + p η ^ 2) (Ici 0) η :=
    fun η hη => (hq η hη).congr_deriv (by ring)
  exact Work.FalknerSkan.MonotoneWindow.hiemenz_monotone_window f p q hf hp hq hf0 hp0 hlim
    (pos_of_abs_le hf hp hq1 hp0 hlim hb)

/-- Homann axisymmetric stagnation-point flow: every solution of f''' + 2 f f'' + 1 − f'² = 0 on
[0, ∞) (f has derivative p, p has derivative q, q has derivative −2 f q − 1 + p², one-sided at 0)
with f(0) = 0, p(0) = 0, p(η) → 1 as η → ∞ and −1 ≤ p ≤ 1 on [0, ∞) has wall shear
q(0) = f''(0) strictly between 1.3119376938 and 1.3119376939. -/
theorem homann_bounded_window (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(2 * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hb : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) :
    1.3119376938 < q 0 ∧ q 0 < 1.3119376939 :=
  Work.FalknerSkan.MonotoneWindow.homann_monotone_window f p q hf hp hq hf0 hp0 hlim
    (pos_of_abs_le hf hp hq hp0 hlim hb)

/-- Hiemenz stagnation-point flow: any two solutions of f''' + f f'' + 1 − f'² = 0 on [0, ∞)
(derivatives one-sided at 0) with f(0) = 0, p(0) = 0, p(η) → 1 as η → ∞ and −1 ≤ p ≤ 1 on
[0, ∞) are equal on [0, ∞): same f, same p = f', same q = f''. -/
theorem hiemenz_bounded_unique (f p q f₂ p₂ q₂ : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hb : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1)
    (hf₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η)
    (hp₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η)
    (hq₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - 1 + p₂ η ^ 2) (Ici 0) η)
    (hf₂0 : f₂ 0 = 0) (hp₂0 : p₂ 0 = 0) (hlim₂ : Tendsto p₂ atTop (𝓝 1))
    (hb₂ : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p₂ η ∧ p₂ η ≤ 1) :
    ∀ η ∈ Ici (0 : ℝ), f η = f₂ η ∧ p η = p₂ η ∧ q η = q₂ η := by
  have hq1 : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(1 * f η * q η) - 1 + p η ^ 2) (Ici 0) η :=
    fun η hη => (hq η hη).congr_deriv (by ring)
  have hq₂1 : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(1 * f₂ η * q₂ η) - 1 + p₂ η ^ 2) (Ici 0) η :=
    fun η hη => (hq₂ η hη).congr_deriv (by ring)
  have hw := Work.FalknerSkan.MonotoneExists.hiemenz_monotone_same_wall_shear f p q f₂ p₂ q₂
    hf hp hq hf0 hp0 hlim (pos_of_abs_le hf hp hq1 hp0 hlim hb)
    hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ (pos_of_abs_le hf₂ hp₂ hq₂1 hp₂0 hlim₂ hb₂)
  exact eq_of_start hf hp hq1 hf₂ hp₂ hq₂1 (hf0.trans hf₂0.symm) (hp0.trans hp₂0.symm) hw

/-- Homann axisymmetric stagnation-point flow: any two solutions of f''' + 2 f f'' + 1 − f'² = 0
on [0, ∞) (derivatives one-sided at 0) with f(0) = 0, p(0) = 0, p(η) → 1 as η → ∞ and
−1 ≤ p ≤ 1 on [0, ∞) are equal on [0, ∞): same f, same p = f', same q = f''. -/
theorem homann_bounded_unique (f p q f₂ p₂ q₂ : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(2 * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hb : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1)
    (hf₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η)
    (hp₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η)
    (hq₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(2 * f₂ η * q₂ η) - 1 + p₂ η ^ 2) (Ici 0) η)
    (hf₂0 : f₂ 0 = 0) (hp₂0 : p₂ 0 = 0) (hlim₂ : Tendsto p₂ atTop (𝓝 1))
    (hb₂ : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p₂ η ∧ p₂ η ≤ 1) :
    ∀ η ∈ Ici (0 : ℝ), f η = f₂ η ∧ p η = p₂ η ∧ q η = q₂ η := by
  have hw := Work.FalknerSkan.MonotoneExists.homann_monotone_same_wall_shear f p q f₂ p₂ q₂
    hf hp hq hf0 hp0 hlim (pos_of_abs_le hf hp hq hp0 hlim hb)
    hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ (pos_of_abs_le hf₂ hp₂ hq₂ hp₂0 hlim₂ hb₂)
  exact eq_of_start hf hp hq hf₂ hp₂ hq₂ (hf0.trans hf₂0.symm) (hp0.trans hp₂0.symm) hw

/-- The monotone solution is in the class: q > 0 and p(0) = 0, p → 1 give 0 ≤ p < 1. -/
theorem bounded_of_pos {p q : ℝ → ℝ}
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1)) (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η) :
    ∀ η ∈ Ici (0 : ℝ), 0 ≤ p η ∧ p η < 1 := by
  intro η hη
  refine ⟨?_, Work.FalknerSkan.CroccoWindow.p_lt_one hp hlim hpos η hη⟩
  have := (Work.FalknerSkan.CroccoWindow.smono_Ici hp hpos).monotoneOn
    (Set.mem_Ici.2 le_rfl) hη hη
  rwa [hp0] at this

/-- Hiemenz stagnation-point flow: there is a solution of f''' + f f'' + 1 − f'² = 0 on [0, ∞)
(f has derivative p, p has derivative q, q has derivative −f q − 1 + p², one-sided at 0) with
f(0) = 0, p(0) = 0, p(η) → 1 as η → ∞, 0 ≤ p < 1 on [0, ∞), and wall shear q(0) = f''(0)
strictly between 1.2325876568 and 1.2325876569. -/
theorem hiemenz_exists_bounded : ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 + p η ^ 2) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧ (∀ η ∈ Ici (0 : ℝ), 0 ≤ p η ∧ p η < 1) ∧
    1.2325876568 < q 0 ∧ q 0 < 1.2325876569 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, hpos, hlo, hhi⟩ :=
    Work.FalknerSkan.MonotoneExists.hiemenz_exists_monotone
  exact ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, bounded_of_pos hp hp0 hlim hpos, hlo, hhi⟩

/-- Homann axisymmetric stagnation-point flow: there is a solution of f''' + 2 f f'' + 1 − f'² = 0
on [0, ∞) (f has derivative p, p has derivative q, q has derivative −2 f q − 1 + p², one-sided at
0) with f(0) = 0, p(0) = 0, p(η) → 1 as η → ∞, 0 ≤ p < 1 on [0, ∞), and wall shear
q(0) = f''(0) strictly between 1.3119376938 and 1.3119376939. -/
theorem homann_exists_bounded : ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(2 * f η * q η) - 1 + p η ^ 2) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧ (∀ η ∈ Ici (0 : ℝ), 0 ≤ p η ∧ p η < 1) ∧
    1.3119376938 < q 0 ∧ q 0 < 1.3119376939 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, hpos, hlo, hhi⟩ :=
    Work.FalknerSkan.MonotoneExists.homann_exists_monotone
  exact ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, bounded_of_pos hp hp0 hlim hpos, hlo, hhi⟩

end Scratch1228

#print axioms Scratch1228.hiemenz_bounded_window
#print axioms Scratch1228.homann_bounded_window
#print axioms Scratch1228.hiemenz_bounded_unique
#print axioms Scratch1228.homann_bounded_unique
#print axioms Scratch1228.hiemenz_exists_bounded
#print axioms Scratch1228.homann_exists_bounded
