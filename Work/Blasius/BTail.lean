import Mathlib

/-!
# Blasius: the analytic half (run 2026-11-07T1228Z)

For solutions of f' = p, p' = q, q' = −f q/2 on [0, ∞) (derivatives within [0, ∞)):
* `zero_back`, `zero_fwd`: q solves a linear equation, so a zero of q anywhere forces q(0) = 0,
  and q(0) = 0 forces q ≡ 0 (Mathlib's ODE uniqueness with a Lipschitz bound from the
  continuity of f on compact intervals);
* `q_pos`: q(0) > 0 gives q > 0 everywhere; `shear_pos`: p(0) = 0 and p → 1 give q(0) > 0;
* `scale`: f(t/c)/c, p(t/c)/c², q(t/c)/c³ is again a solution for every c > 0;
* `tail`: past a time L where f ≥ m > 0 and p ≥ 0, p stays in [p(L), p(L) + (2/m) q(L)]
  (p + (2/m) q is non-increasing there).
-/

namespace Work.Blasius.BTail
open Set Filter Topology

/-- f' = p, p' = q, q' = −f q/2 at every η ≥ 0, derivatives within [0, ∞). -/
structure IsSol (f p q : ℝ → ℝ) : Prop where
  hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η
  hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η
  hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η / 2)) (Ici 0) η

variable {f p q : ℝ → ℝ}

theorem at_pos {u u' : ℝ → ℝ} (h : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt u (u' η) (Ici 0) η)
    {x : ℝ} (hx : 0 < x) : HasDerivAt u (u' x) x :=
  (h x (le_of_lt hx)).hasDerivAt (Ici_mem_nhds hx)

theorem contOn {u u' : ℝ → ℝ} (h : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt u (u' η) (Ici 0) η) :
    ContinuousOn u (Ici 0) := fun η hη => (h η hη).continuousWithinAt

theorem lip_lin {c M : ℝ} (hc : |c| ≤ M) :
    LipschitzOnWith (Real.toNNReal (M / 2)) (fun y : ℝ => -(c * y / 2)) univ := by
  have hM : 0 ≤ M := (abs_nonneg c).trans hc
  refine LipschitzOnWith.of_dist_le_mul fun x _ y _ => ?_
  rw [Real.coe_toNNReal _ (by linarith)]
  simp only [Real.dist_eq]
  have e : -(c * x / 2) - -(c * y / 2) = -(c / 2) * (x - y) := by ring
  rw [e, abs_mul, abs_neg, abs_div, abs_two]
  exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)

theorem bound_on (S : IsSol f p q) (b : ℝ) : ∃ M, ∀ t ∈ Icc (0 : ℝ) b, |f t| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := b)).exists_bound_of_continuousOn
    ((contOn S.hf).mono Icc_subset_Ici_self)
  exact ⟨M, fun t ht => by simpa using hM t ht⟩

/-- A zero of q at t₁ ≥ 0 forces q(0) = 0. -/
theorem zero_back (S : IsSol f p q) {t₁ : ℝ} (ht : 0 ≤ t₁) (hz : q t₁ = 0) : q 0 = 0 := by
  obtain ⟨M, hM⟩ := bound_on S t₁
  have h := ODE_solution_unique_of_mem_Icc_left (v := fun t y => -(f t * y / 2))
    (s := fun _ => univ) (K := Real.toNNReal (M / 2)) (a := 0) (b := t₁) (f := q)
    (g := fun _ => 0)
    (fun t ht' => lip_lin (hM t ⟨ht'.1.le, ht'.2⟩))
    ((contOn S.hq).mono Icc_subset_Ici_self)
    (fun t ht' => (at_pos S.hq ht'.1).hasDerivWithinAt)
    (fun _ _ => mem_univ _) continuousOn_const
    (fun t _ => by simp only [mul_zero, zero_div, neg_zero]; exact hasDerivWithinAt_const _ _ _)
    (fun _ _ => mem_univ _) hz
  exact h ⟨le_rfl, ht⟩

/-- q(0) = 0 forces q = 0 on [0, ∞). -/
theorem zero_fwd (S : IsSol f p q) (hz : q 0 = 0) : ∀ t ∈ Ici (0 : ℝ), q t = 0 := by
  intro t ht
  obtain ⟨M, hM⟩ := bound_on S t
  have h := ODE_solution_unique_of_mem_Icc_right (v := fun t y => -(f t * y / 2))
    (s := fun _ => univ) (K := Real.toNNReal (M / 2)) (a := 0) (b := t) (f := q)
    (g := fun _ => 0)
    (fun u hu => lip_lin (hM u ⟨hu.1, hu.2.le⟩))
    ((contOn S.hq).mono Icc_subset_Ici_self)
    (fun u hu => (S.hq u hu.1).mono (Ici_subset_Ici.2 hu.1))
    (fun _ _ => mem_univ _) continuousOn_const
    (fun u _ => by simp only [mul_zero, zero_div, neg_zero]; exact hasDerivWithinAt_const _ _ _)
    (fun _ _ => mem_univ _) hz
  exact h ⟨ht, le_rfl⟩

/-- q(0) > 0 gives q > 0 on [0, ∞). -/
theorem q_pos (S : IsSol f p q) (h0 : 0 < q 0) : ∀ t ∈ Ici (0 : ℝ), 0 < q t := by
  intro t ht
  by_contra hneg
  push_neg at hneg
  obtain ⟨u, hu, hqu⟩ := intermediate_value_Icc' (show (0 : ℝ) ≤ t from ht)
    ((contOn S.hq).mono Icc_subset_Ici_self) ⟨hneg, h0.le⟩
  have := zero_back S hu.1 hqu
  linarith

/-- q(0) < 0 gives q < 0 on [0, ∞). -/
theorem q_neg (S : IsSol f p q) (h0 : q 0 < 0) : ∀ t ∈ Ici (0 : ℝ), q t < 0 := by
  intro t ht
  by_contra hpos
  push_neg at hpos
  obtain ⟨u, hu, hqu⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ t from ht)
    ((contOn S.hq).mono Icc_subset_Ici_self) ⟨h0.le, hpos⟩
  have := zero_back S hu.1 hqu
  linarith

/-- p(0) = 0 and p → 1 force q(0) > 0. -/
theorem shear_pos (S : IsSol f p q) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1)) :
    0 < q 0 := by
  by_contra hle
  push_neg at hle
  have hq : ∀ t ∈ Ici (0 : ℝ), q t ≤ 0 := by
    rcases hle.lt_or_eq with h | h
    · exact fun t ht => (q_neg S h t ht).le
    · exact fun t ht => (zero_fwd S h t ht).le
  have hanti : AntitoneOn p (Ici 0) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0) (f' := q) (contOn S.hp) ?_ ?_
    · intro x hx
      rw [interior_Ici] at hx ⊢
      exact (at_pos S.hp hx).hasDerivWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      exact hq x (mem_Ici.2 (le_of_lt hx))
  have hev := (hlim.eventually (lt_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num))).and
    (eventually_ge_atTop (0 : ℝ))
  obtain ⟨t, ht1, ht0⟩ := hev.exists
  have := hanti (show (0 : ℝ) ∈ Ici 0 from mem_Ici.2 le_rfl) ht0 ht0
  linarith

/-- Scaling: f(t/c)/c, p(t/c)/c², q(t/c)/c³ is a solution for every c > 0. -/
theorem scale (S : IsSol f p q) {c : ℝ} (hc : 0 < c) :
    IsSol (fun t => f (t / c) / c) (fun t => p (t / c) / c ^ 2) (fun t => q (t / c) / c ^ 3) := by
  have hmaps : MapsTo (fun x : ℝ => x / c) (Ici 0) (Ici 0) := fun x hx => div_nonneg hx hc.le
  have hd : ∀ η : ℝ, HasDerivWithinAt (fun x : ℝ => x / c) (1 / c) (Ici 0) η := fun η => by
    simpa using (hasDerivWithinAt_id η (Ici (0 : ℝ))).div_const c
  have hc0 : c ≠ 0 := hc.ne'
  refine ⟨fun η hη => ?_, fun η hη => ?_, fun η hη => ?_⟩
  · have h := ((S.hf (η / c) (hmaps hη)).comp η (hd η) hmaps).div_const c
    refine HasDerivWithinAt.congr_deriv h ?_
    field_simp
  · have h := ((S.hp (η / c) (hmaps hη)).comp η (hd η) hmaps).div_const (c ^ 2)
    refine HasDerivWithinAt.congr_deriv h ?_
    field_simp
  · have h := ((S.hq (η / c) (hmaps hη)).comp η (hd η) hmaps).div_const (c ^ 3)
    refine HasDerivWithinAt.congr_deriv h ?_
    field_simp

/-- The tail: past L, where f ≥ m > 0 and p ≥ 0, p stays in [p(L), p(L) + (2/m) q(L)]
whenever q > 0 on [0, ∞). -/
theorem tail (S : IsSol f p q) (hpos : ∀ t ∈ Ici (0 : ℝ), 0 < q t) {L m : ℝ} (hL : 0 ≤ L)
    (hm : 0 < m) (hfL : m ≤ f L) (hpL : 0 ≤ p L) :
    ∀ t ∈ Ici L, p L ≤ p t ∧ p t ≤ p L + 2 / m * q L := by
  have hpmono : MonotoneOn p (Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) (f' := q) (contOn S.hp) ?_ ?_
    · intro x hx
      rw [interior_Ici] at hx ⊢
      exact (at_pos S.hp hx).hasDerivWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      exact (hpos x (mem_Ici.2 (le_of_lt hx))).le
  have hpge : ∀ t ∈ Ici L, p L ≤ p t := fun t ht =>
    hpmono (show L ∈ Ici (0 : ℝ) from hL) (show t ∈ Ici (0 : ℝ) from hL.trans ht) ht
  have hfmono : MonotoneOn f (Ici L) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici L) (f' := p)
      ((contOn S.hf).mono (Ici_subset_Ici.2 hL)) ?_ ?_
    · intro x hx
      rw [interior_Ici] at hx ⊢
      exact (at_pos S.hf (lt_of_le_of_lt hL hx)).hasDerivWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      exact hpL.trans (hpge x (mem_Ici.2 (le_of_lt hx)))
  have hfge : ∀ t ∈ Ici L, m ≤ f t := fun t ht =>
    hfL.trans (hfmono (show L ∈ Ici L from mem_Ici.2 le_rfl) ht ht)
  have hW : AntitoneOn (fun t => p t + 2 / m * q t) (Ici L) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici L)
      (f' := fun t => q t + 2 / m * (-(f t * q t / 2)))
      (((contOn S.hp).add ((contOn S.hq).const_smul (2 / m))).mono (Ici_subset_Ici.2 hL)) ?_ ?_
    · intro x hx
      rw [interior_Ici] at hx ⊢
      have hx0 : 0 < x := lt_of_le_of_lt hL hx
      exact ((at_pos S.hp hx0).add ((at_pos S.hq hx0).const_mul (2 / m))).hasDerivWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hqx := hpos x (hL.trans (le_of_lt hx))
      have hfx := hfge x (mem_Ici.2 (le_of_lt hx))
      have e : q x + 2 / m * (-(f x * q x / 2)) = q x * (m - f x) / m := by
        field_simp; ring
      rw [e]
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos hqx.le (by linarith)) hm.le
  intro t ht
  refine ⟨hpge t ht, ?_⟩
  have h1 := hW (show L ∈ Ici L from mem_Ici.2 le_rfl) ht ht
  have hqt := hpos t (hL.trans ht)
  have h2 : 0 < 2 / m * q t := mul_pos (by positivity) hqt
  simp only at h1
  linarith

end Work.Blasius.BTail
