import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
/-! A global solution of the boundary-layer system f' = p, p' = q, q' = −c f q + β (p² − 1) on [0, ∞) from the wall values f = 0, p = 0 and q = 10, for every c in [1, 2] and every β in (0, 1], whose shear stays positive. The solution is the flow of the field clamped at a level growing like an exponential in η (Picard–Lindelöf on every [0, T], glued by uniqueness); the clamps are never active: up to one fifth the shear stays between eight and twelve, after it the shear stays positive, below twenty times the velocity, and the velocity grows at most like an exponential (continuous induction, `cont_ind`). Module `ExpFlow`. -/

namespace Checked.Trust.ExpFlow
open Set Filter

/-- Clamp to [−C, C]. -/
noncomputable def ecl (C y : ℝ) : ℝ := max (-C) (min C y)

theorem ecl_sub (C y z : ℝ) : |ecl C y - ecl C z| ≤ |y - z| := by
  unfold ecl
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le (by simp) ?_)
  exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le (by simp) le_rfl)

theorem abs_ecl_le {C : ℝ} (hC : 0 ≤ C) (y : ℝ) : |ecl C y| ≤ C := by
  unfold ecl; rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem ecl_of_abs_le {C y : ℝ} (h : |y| ≤ C) : ecl C y = y := by
  unfold ecl
  rw [abs_le] at h
  rw [min_eq_right h.2, max_eq_right h.1]

theorem ecl_nonneg {C y : ℝ} (hC : 0 ≤ C) (hy : 0 ≤ y) : 0 ≤ ecl C y := by
  unfold ecl
  exact le_max_of_le_right (le_min hC hy)

/-- The clamp level. -/
noncomputable def M (t : ℝ) : ℝ := 100 * Real.exp (20 * t)

theorem M_pos (t : ℝ) : 0 < M t := by unfold M; positivity

theorem M_mono {t T : ℝ} (h : t ≤ T) : M t ≤ M T := by
  unfold M
  have := Real.exp_le_exp.mpr (by linarith : 20 * t ≤ 20 * T)
  linarith

/-- The clamped field. -/
noncomputable def vE (c β : ℝ) (t : ℝ) (y : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (ecl (M t) y.2.1, ecl (M t) y.2.2,
    -(c * ecl (M t) y.1 * ecl (M t) y.2.2) + β * (ecl (M t) y.2.1 ^ 2 - 1))

section flow
variable {c β : ℝ} (hc0 : 0 ≤ c) (hc2 : c ≤ 2) (hb0 : 0 ≤ β) (hb1 : β ≤ 1)
include hc0 hc2 hb0 hb1

theorem lip {T t : ℝ} (ht : t ∈ Icc 0 T) :
    LipschitzWith (Real.toNNReal (6 * M T + 1)) (vE c β t) := by
  have hMT := M_pos T
  refine LipschitzWith.of_dist_le_mul fun y z => ?_
  rw [Real.coe_toNNReal _ (by linarith)]
  simp only [vE, Prod.dist_eq, Real.dist_eq]
  set m := max |y.1 - z.1| (max |y.2.1 - z.2.1| |y.2.2 - z.2.2|)
  have hd1 : |y.1 - z.1| ≤ m := le_max_left _ _
  have hd2 : |y.2.1 - z.2.1| ≤ m := (le_max_left _ _).trans (le_max_right _ _)
  have hd3 : |y.2.2 - z.2.2| ≤ m := (le_max_right _ _).trans (le_max_right _ _)
  have hm : 0 ≤ m := (abs_nonneg _).trans hd1
  set C := M t with hCdef
  have hC0 : 0 ≤ C := (M_pos t).le
  have hCT : C ≤ M T := M_mono ht.2
  refine max_le ?_ (max_le ?_ ?_)
  · have := ecl_sub C y.2.1 z.2.1; nlinarith
  · have := ecl_sub C y.2.2 z.2.2; nlinarith
  · set a := ecl C y.1
    set a' := ecl C z.1
    set b := ecl C y.2.2
    set b' := ecl C z.2.2
    set d := ecl C y.2.1
    set d' := ecl C z.2.1
    have ha : |a - a'| ≤ |y.1 - z.1| := ecl_sub C y.1 z.1
    have hb : |b - b'| ≤ |y.2.2 - z.2.2| := ecl_sub C y.2.2 z.2.2
    have hd : |d - d'| ≤ |y.2.1 - z.2.1| := ecl_sub C y.2.1 z.2.1
    have hbb : |b| ≤ C := abs_ecl_le hC0 _
    have haa : |a'| ≤ C := abs_ecl_le hC0 _
    have hdd : |d| ≤ C := abs_ecl_le hC0 _
    have hdd' : |d'| ≤ C := abs_ecl_le hC0 _
    have e : -(c * a * b) + β * (d ^ 2 - 1) - (-(c * a' * b') + β * (d' ^ 2 - 1))
        = -(c * ((a - a') * b + a' * (b - b'))) + β * ((d + d') * (d - d')) := by ring
    rw [e]
    have h1 : |(a - a') * b| ≤ C * m := by
      rw [abs_mul, mul_comm]
      exact mul_le_mul hbb (ha.trans hd1) (abs_nonneg _) hC0
    have h2 : |a' * (b - b')| ≤ C * m := by
      rw [abs_mul]
      exact mul_le_mul haa (hb.trans hd3) (abs_nonneg _) hC0
    have h4 : |(d + d') * (d - d')| ≤ (2 * C) * m := by
      rw [abs_mul]
      have : |d + d'| ≤ 2 * C := (abs_add_le d d').trans (by linarith)
      exact mul_le_mul this (hd.trans hd2) (abs_nonneg _) (by linarith)
    have h3 := abs_add_le ((a - a') * b) (a' * (b - b'))
    have h5 := abs_add_le (-(c * ((a - a') * b + a' * (b - b')))) (β * ((d + d') * (d - d')))
    rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg hc0, abs_of_nonneg hb0] at h5
    have h6 : c * |(a - a') * b + a' * (b - b')| ≤ 2 * (2 * C * m) :=
      mul_le_mul hc2 (by linarith) (abs_nonneg _) (by norm_num)
    have h7 : β * |(d + d') * (d - d')| ≤ 1 * (2 * C * m) :=
      mul_le_mul hb1 (by linarith) (abs_nonneg _) (by norm_num)
    nlinarith

theorem norm_le {T t : ℝ} (ht : t ∈ Icc 0 T) (y : ℝ × ℝ × ℝ) :
    ‖vE c β t y‖ ≤ 3 * M T ^ 2 + M T + 1 := by
  have hMT := M_pos T
  simp only [vE, Prod.norm_def, Real.norm_eq_abs]
  set C := M t with hCdef
  have hC0 : 0 ≤ C := (M_pos t).le
  have hCT : C ≤ M T := M_mono ht.2
  have h1 := abs_ecl_le hC0 y.2.1
  have h2 := abs_ecl_le hC0 y.2.2
  have h3 := abs_ecl_le hC0 y.1
  have hCC : C ^ 2 ≤ M T ^ 2 := by nlinarith
  refine max_le (by nlinarith) (max_le (by nlinarith) ?_)
  have hab : |ecl C y.1 * ecl C y.2.2| ≤ C * C := by
    rw [abs_mul]; exact mul_le_mul h3 h2 (abs_nonneg _) hC0
  have hcab : |c * ecl C y.1 * ecl C y.2.2| ≤ 2 * (C * C) := by
    rw [mul_assoc, abs_mul, abs_of_nonneg hc0]
    exact mul_le_mul hc2 hab (abs_nonneg _) (by norm_num)
  have hsq : |ecl C y.2.1 ^ 2 - 1| ≤ C * C + 1 := by
    refine (abs_sub _ _).trans ?_
    rw [abs_pow, abs_one]; nlinarith [abs_nonneg (ecl C y.2.1)]
  have hbsq : |β * (ecl C y.2.1 ^ 2 - 1)| ≤ 1 * (C * C + 1) := by
    rw [abs_mul, abs_of_nonneg hb0]
    exact mul_le_mul hb1 hsq (abs_nonneg _) (by norm_num)
  have k1 := abs_add_le (-(c * ecl C y.1 * ecl C y.2.2)) (β * (ecl C y.2.1 ^ 2 - 1))
  rw [abs_neg] at k1
  nlinarith

omit hc0 hc2 hb0 hb1 in
theorem cont (y : ℝ × ℝ × ℝ) : Continuous (fun t => vE c β t y) := by
  unfold vE ecl M
  fun_prop

/-- A solution on [0, T] for every T > 0. -/
theorem local_sol (y0 : ℝ × ℝ × ℝ) (T : ℝ) (hT : 0 < T) : ∃ Y : ℝ → ℝ × ℝ × ℝ, Y 0 = y0 ∧
    ∀ t ∈ Icc 0 T, HasDerivWithinAt Y (vE c β t (Y t)) (Icc 0 T) t := by
  set L : ℝ := 3 * M T ^ 2 + M T + 1 with hL
  have hL0 : 0 ≤ L := by have := M_pos T; positivity
  have hPL : IsPicardLindelof (vE c β) (tmin := 0) (tmax := T) ⟨0, le_rfl, hT.le⟩
      y0 (Real.toNNReal (L * T)) 0 (Real.toNNReal L)
      (Real.toNNReal (6 * M T + 1)) :=
    { lipschitzOnWith := fun t ht => (lip hc0 hc2 hb0 hb1 ht).lipschitzOnWith
      continuousOn := fun x _ => (cont x).continuousOn
      norm_le := fun t ht p _ => by
        rw [Real.coe_toNNReal _ hL0]; exact norm_le hc0 hc2 hb0 hb1 ht p
      mul_max_le := by
        rw [Real.coe_toNNReal _ hL0, Real.coe_toNNReal _ (by positivity)]
        simp only [NNReal.coe_zero, sub_zero, sub_self]
        rw [max_eq_left hT.le] }
  exact hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

/-- Forward uniqueness on [0, T]. -/
theorem unique_right {T : ℝ} (_hT : 0 ≤ T) {Y Z : ℝ → ℝ × ℝ × ℝ}
    (hY : ∀ t ∈ Icc 0 T, HasDerivWithinAt Y (vE c β t (Y t)) (Icc 0 T) t)
    (hZ : ∀ t ∈ Icc 0 T, HasDerivWithinAt Z (vE c β t (Z t)) (Icc 0 T) t)
    (h0 : Y 0 = Z 0) : EqOn Y Z (Icc 0 T) := by
  refine ODE_solution_unique_of_mem_Icc_right (v := vE c β) (s := fun _ => univ)
    (K := Real.toNNReal (6 * M T + 1))
    (fun t ht => (lip hc0 hc2 hb0 hb1 (Ico_subset_Icc_self ht)).lipschitzOnWith)
    (fun t ht => (hY t ht).continuousWithinAt) (fun t ht => ?_) (fun _ _ => mem_univ _)
    (fun t ht => (hZ t ht).continuousWithinAt) (fun t ht => ?_) (fun _ _ => mem_univ _) h0
  · have hmem : t ∈ Icc 0 T := ⟨ht.1, ht.2.le⟩
    refine (hY t hmem).mono_of_mem_nhdsWithin ?_
    exact Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)
  · have hmem : t ∈ Icc 0 T := ⟨ht.1, ht.2.le⟩
    refine (hZ t hmem).mono_of_mem_nhdsWithin ?_
    exact Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)

theorem exists_sol (y0 : ℝ × ℝ × ℝ) : ∃ Y : ℝ → ℝ × ℝ × ℝ, Y 0 = y0 ∧
    ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt Y (vE c β t (Y t)) (Ici 0) t := by
  have hex : ∀ n : ℕ, ∃ Y : ℝ → ℝ × ℝ × ℝ, Y 0 = y0 ∧
      ∀ t ∈ Icc 0 ((n : ℝ) + 1), HasDerivWithinAt Y (vE c β t (Y t)) (Icc 0 ((n : ℝ) + 1)) t :=
    fun n => local_sol hc0 hc2 hb0 hb1 y0 _ (by positivity)
  choose sol hsol0 hsol using hex
  have hag : ∀ k n : ℕ, ∀ s ∈ Icc (0 : ℝ) ((k : ℝ) + 1), s ≤ (n : ℝ) + 1 → sol k s = sol n s := by
    intro k n s hs hsn
    rcases le_total k n with hkn | hnk
    · have hkn' : (k : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hkn 1
      exact unique_right hc0 hc2 hb0 hb1 (by positivity) (hsol k)
        (fun t ht => (hsol n t ⟨ht.1, ht.2.trans hkn'⟩).mono (Icc_subset_Icc_right hkn'))
        ((hsol0 k).trans (hsol0 n).symm) hs
    · have hnk' : (n : ℝ) + 1 ≤ (k : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hnk 1
      exact (unique_right hc0 hc2 hb0 hb1 (by positivity) (hsol n)
        (fun t ht => (hsol k t ⟨ht.1, ht.2.trans hnk'⟩).mono (Icc_subset_Icc_right hnk'))
        ((hsol0 n).trans (hsol0 k).symm) ⟨hs.1, hsn⟩).symm
  refine ⟨fun t => sol (⌈t⌉₊) t, ?_, fun t ht => ?_⟩
  · simp [hsol0]
  · set n := ⌈t⌉₊ with hn
    have htn : t ≤ (n : ℝ) := Nat.le_ceil t
    have hlt : t < (n : ℝ) + 1 := by linarith
    have heq : ∀ s ∈ Ico (0 : ℝ) ((n : ℝ) + 1), sol (⌈s⌉₊) s = sol n s := by
      intro s hs
      refine hag _ n s ⟨hs.1, ?_⟩ hs.2.le
      have := Nat.le_ceil s; linarith
    have hnhds : Ico (0 : ℝ) ((n : ℝ) + 1) ∈ nhdsWithin t (Ici 0) := by
      have : Iio ((n : ℝ) + 1) ∈ nhds t := Iio_mem_nhds hlt
      have h2 := inter_mem_nhdsWithin (Ici (0 : ℝ)) this
      refine Filter.mem_of_superset h2 ?_
      intro s hs; exact ⟨hs.1, hs.2⟩
    have hd := (hsol n t ⟨ht, hlt.le⟩).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset hnhds (fun s hs => ⟨hs.1, hs.2.le⟩))
    have ht0 : sol (⌈t⌉₊) t = sol n t := rfl
    simp only
    rw [ht0]
    refine hd.congr_of_eventuallyEq ?_ (heq t ⟨ht, hlt⟩)
    exact Filter.mem_of_superset hnhds (fun s hs => heq s hs)

end flow

/-- Continuous induction on [a, b]: positivity at a, and positivity at every later point of the
interval from positivity before it, give positivity on the whole interval. -/
theorem cont_ind {a b : ℝ} {g : ℝ → ℝ} (hg : ContinuousOn g (Icc a b)) (ha : 0 < g a)
    (hstep : ∀ t ∈ Ioc a b, (∀ s ∈ Ico a t, 0 < g s) → 0 < g t) : ∀ t ∈ Icc a b, 0 < g t := by
  by_contra hne
  push Not at hne
  obtain ⟨t0, ht0, hgt0⟩ := hne
  have hScl : IsClosed (Icc a b ∩ g ⁻¹' Iic 0) :=
    hg.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hSne : (Icc a b ∩ g ⁻¹' Iic 0).Nonempty := ⟨t0, ht0, hgt0⟩
  have hSbdd : BddBelow (Icc a b ∩ g ⁻¹' Iic 0) := ⟨a, fun t ht => ht.1.1⟩
  have hτS := hScl.csInf_mem hSne hSbdd
  have hτg : g (sInf (Icc a b ∩ g ⁻¹' Iic 0)) ≤ 0 := hτS.2
  have hτa : a < sInf (Icc a b ∩ g ⁻¹' Iic 0) := by
    rcases eq_or_lt_of_le hτS.1.1 with h | h
    · rw [← h] at hτg; linarith
    · exact h
  have hpos := hstep _ ⟨hτa, hτS.1.2⟩ (fun s hs => by
    by_contra h
    push Not at h
    have : sInf (Icc a b ∩ g ⁻¹' Iic 0) ≤ s :=
      csInf_le hSbdd ⟨⟨hs.1, hs.2.le.trans hτS.1.2⟩, h⟩
    linarith [hs.2])
  linarith

/-- A function with a nonnegative derivative inside [a, t], continuous on [0, ∞) with 0 ≤ a,
does not decrease from a to t. -/
theorem le_of_deriv {g g' : ℝ → ℝ} {a t : ℝ} (ha : 0 ≤ a) (hat : a ≤ t)
    (hc : ContinuousOn g (Ici 0)) (hd : ∀ s ∈ Ioo a t, HasDerivAt g (g' s) s)
    (hn : ∀ s ∈ Ioo a t, 0 ≤ g' s) : g a ≤ g t := by
  have hc' : ContinuousOn g (Icc a t) := hc.mono (fun x hx => le_trans ha hx.1)
  have hmono := monotoneOn_of_deriv_nonneg (convex_Icc a t) hc'
    (fun s hs => by
      rw [interior_Icc] at hs; exact (hd s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => by rw [interior_Icc] at hs; rw [(hd s hs).deriv]; exact hn s hs)
  exact hmono ⟨le_rfl, hat⟩ ⟨hat, le_rfl⟩ hat

theorem M_ge {s : ℝ} (hs : 0 ≤ s) : 100 ≤ M s := by
  unfold M
  have := Real.one_le_exp (by linarith : 0 ≤ 20 * s)
  linarith

theorem M_cont : Continuous M := by unfold M; fun_prop

section bounds
variable {c β : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2) (hb0 : 0 < β) (hb1 : β ≤ 1)
  (f p q : ℝ → ℝ)
  (hf' : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt f (ecl (M t) (p t)) (Ici 0) t)
  (hp' : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt p (ecl (M t) (q t)) (Ici 0) t)
  (hq' : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt q
    (-(c * ecl (M t) (f t) * ecl (M t) (q t)) + β * (ecl (M t) (p t) ^ 2 - 1)) (Ici 0) t)
  (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hq0 : q 0 = 10)
include hc1 hc2 hb0 hb1 hf' hp' hq' hf0 hp0 hq0

omit hc1 hc2 hb0 hb1 hq' hf0 hp0 hq0 in
theorem conts : ContinuousOn f (Ici 0) ∧ ContinuousOn p (Ici 0) := by
  exact ⟨fun t ht => (hf' t ht).continuousWithinAt, fun t ht => (hp' t ht).continuousWithinAt⟩

/-- Up to one fifth: with the shear between eight and twelve before t, the velocity and f are
enclosed up to t, and the shear at t is between ten minus seven t and ten plus six t. -/
theorem phase1 {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 5)) (hq : ∀ s ∈ Ico 0 t, 8 < q s ∧ q s < 12) :
    (∀ s ∈ Icc 0 t, 8 * s ≤ p s ∧ p s ≤ 12 * s ∧ 4 * (s * s) ≤ f s ∧ f s ≤ 6 * (s * s)) ∧
    10 - 7 * t ≤ q t ∧ q t ≤ 10 + 6 * t := by
  have hfc : ContinuousOn f (Ici 0) := fun t ht => (hf' t ht).continuousWithinAt
  have hpc : ContinuousOn p (Ici 0) := fun t ht => (hp' t ht).continuousWithinAt
  have hqc : ContinuousOn q (Ici 0) := fun t ht => (hq' t ht).continuousWithinAt
  -- derivative of p inside (0, t)
  have hpd : ∀ s ∈ Ioo 0 t, HasDerivAt p (q s) s := by
    intro s hs
    have h := (hp' s hs.1.le).hasDerivAt (Ici_mem_nhds hs.1)
    have hqs := hq s ⟨hs.1.le, hs.2⟩
    have hM := M_ge hs.1.le
    rwa [ecl_of_abs_le (abs_le.mpr ⟨by linarith, by linarith⟩)] at h
  have hP : ∀ s ∈ Icc 0 t, 8 * s ≤ p s ∧ p s ≤ 12 * s := by
    intro s hs
    have hsub : ∀ r ∈ Ioo 0 s, r ∈ Ioo 0 t := fun r hr => ⟨hr.1, hr.2.trans_le hs.2⟩
    constructor
    · have := le_of_deriv (g := fun r => p r - 8 * r) (g' := fun r => q r - 8) le_rfl hs.1
        (hpc.sub (continuous_const.mul continuous_id).continuousOn)
        (fun r hr => ((hpd r (hsub r hr)).sub ((hasDerivAt_id' r).const_mul 8)).congr_deriv
          (by ring))
        (fun r hr => by have := hq r ⟨hr.1.le, (hsub r hr).2⟩; linarith)
      simp only [hp0] at this; linarith
    · have := le_of_deriv (g := fun r => 12 * r - p r) (g' := fun r => 12 - q r) le_rfl hs.1
        ((continuous_const.mul continuous_id).continuousOn.sub hpc)
        (fun r hr => (((hasDerivAt_id' r).const_mul 12).sub (hpd r (hsub r hr))).congr_deriv
          (by ring))
        (fun r hr => by have := hq r ⟨hr.1.le, (hsub r hr).2⟩; linarith)
      simp only [hp0] at this; linarith
  have hfd : ∀ s ∈ Ioo 0 t, HasDerivAt f (p s) s := by
    intro s hs
    have h := (hf' s hs.1.le).hasDerivAt (Ici_mem_nhds hs.1)
    have hps := hP s ⟨hs.1.le, hs.2.le⟩
    have hM := M_ge hs.1.le
    have : s ≤ 1 / 5 := hs.2.le.trans ht.2
    rwa [ecl_of_abs_le (abs_le.mpr ⟨by linarith, by linarith⟩)] at h
  have hF : ∀ s ∈ Icc 0 t, 4 * (s * s) ≤ f s ∧ f s ≤ 6 * (s * s) := by
    intro s hs
    have hsub : ∀ r ∈ Ioo 0 s, r ∈ Ioo 0 t := fun r hr => ⟨hr.1, hr.2.trans_le hs.2⟩
    constructor
    · have := le_of_deriv (g := fun r => f r - 4 * (r * r)) (g' := fun r => p r - 8 * r)
        le_rfl hs.1
        (hfc.sub (continuous_const.mul (continuous_id.mul continuous_id)).continuousOn)
        (fun r hr => ((hfd r (hsub r hr)).sub
          (((hasDerivAt_id' r).mul (hasDerivAt_id' r)).const_mul 4)).congr_deriv (by ring))
        (fun r hr => by have := hP r ⟨hr.1.le, (hsub r hr).2.le⟩; linarith)
      simp only [hf0] at this; linarith
    · have := le_of_deriv (g := fun r => 6 * (r * r) - f r) (g' := fun r => 12 * r - p r)
        le_rfl hs.1
        ((continuous_const.mul (continuous_id.mul continuous_id)).continuousOn.sub hfc)
        (fun r hr => ((((hasDerivAt_id' r).mul (hasDerivAt_id' r)).const_mul 6).sub
          (hfd r (hsub r hr))).congr_deriv (by ring))
        (fun r hr => by have := hP r ⟨hr.1.le, (hsub r hr).2.le⟩; linarith)
      simp only [hf0] at this; linarith
  have hqd : ∀ s ∈ Ioo 0 t, HasDerivAt q (-(c * f s * q s) + β * (p s ^ 2 - 1)) s := by
    intro s hs
    have h := (hq' s hs.1.le).hasDerivAt (Ici_mem_nhds hs.1)
    have hps := hP s ⟨hs.1.le, hs.2.le⟩
    have hfs := hF s ⟨hs.1.le, hs.2.le⟩
    have hqs := hq s ⟨hs.1.le, hs.2⟩
    have hM := M_ge hs.1.le
    have : s ≤ 1 / 5 := hs.2.le.trans ht.2
    have hs0 := hs.1
    rwa [ecl_of_abs_le (y := f s) (abs_le.mpr ⟨by nlinarith, by nlinarith⟩),
      ecl_of_abs_le (y := q s) (abs_le.mpr ⟨by linarith, by linarith⟩),
      ecl_of_abs_le (y := p s) (abs_le.mpr ⟨by linarith, by linarith⟩)] at h
  refine ⟨fun s hs => ⟨(hP s hs).1, (hP s hs).2, (hF s hs).1, (hF s hs).2⟩, ?_, ?_⟩
  · have := le_of_deriv (g := fun r => q r + 7 * r)
      (g' := fun r => -(c * f r * q r) + β * (p r ^ 2 - 1) + 7) le_rfl ht.1
      (hqc.add (continuous_const.mul continuous_id).continuousOn)
      (fun r hr => ((hqd r hr).add ((hasDerivAt_id' r).const_mul 7)).congr_deriv (by ring))
      (fun r hr => by
        have hps := hP r ⟨hr.1.le, hr.2.le⟩
        have hfs := hF r ⟨hr.1.le, hr.2.le⟩
        have hqs := hq r ⟨hr.1.le, hr.2⟩
        have hr5 : r ≤ 1 / 5 := hr.2.le.trans ht.2
        have hfq : c * f r * q r ≤ 2 * (6 * (1 / 25)) * 12 := by
          have h1 : f r ≤ 6 * (1 / 25) := by nlinarith [hr.1]
          have h2 : 0 ≤ f r := by nlinarith [hr.1]
          have h3 : c * f r ≤ 2 * (6 * (1 / 25)) := by nlinarith
          nlinarith
        nlinarith [sq_nonneg (p r)])
    simp only [hq0] at this; linarith
  · have := le_of_deriv (g := fun r => 6 * r - q r)
      (g' := fun r => 6 - (-(c * f r * q r) + β * (p r ^ 2 - 1))) le_rfl ht.1
      ((continuous_const.mul continuous_id).continuousOn.sub hqc)
      (fun r hr => (((hasDerivAt_id' r).const_mul 6).sub (hqd r hr)).congr_deriv (by ring))
      (fun r hr => by
        have hps := hP r ⟨hr.1.le, hr.2.le⟩
        have hfs := hF r ⟨hr.1.le, hr.2.le⟩
        have hqs := hq r ⟨hr.1.le, hr.2⟩
        have hr5 : r ≤ 1 / 5 := hr.2.le.trans ht.2
        have h2 : 0 ≤ f r := by nlinarith [hr.1]
        have hfq : 0 ≤ c * f r * q r := by
          have : 0 ≤ c * f r := mul_nonneg (by linarith) h2
          exact mul_nonneg this (by linarith)
        have hp2 : p r ^ 2 ≤ (12 / 5) ^ 2 := by nlinarith [hr.1]
        have hbp : β * (p r ^ 2 - 1) ≤ 1 * ((12 / 5) ^ 2) := by
          have : p r ^ 2 - 1 ≤ (12 / 5) ^ 2 := by linarith
          nlinarith [sq_nonneg (p r)]
        nlinarith)
    simp only [hq0] at this; linarith

omit hf0 hp0 hq0 in
/-- After one fifth: the shear and f stay positive, the shear stays below twenty times the velocity,
and f and twenty times the velocity stay below the clamp level. -/
theorem phase2 (ha : 8 / 5 ≤ p (1 / 5) ∧ p (1 / 5) ≤ 12 / 5 ∧ 4 / 25 ≤ f (1 / 5) ∧
      f (1 / 5) ≤ 6 / 25 ∧ 8 < q (1 / 5) ∧ q (1 / 5) < 12) {T : ℝ} :
    ∀ t ∈ Icc (1 / 5 : ℝ) T, 0 < min (min (q t) (f t))
      (min (20 * p t - q t) (min (M t - f t) (M t - 20 * p t))) := by
  have hfc : ContinuousOn f (Ici 0) := fun t ht => (hf' t ht).continuousWithinAt
  have hpc : ContinuousOn p (Ici 0) := fun t ht => (hp' t ht).continuousWithinAt
  have hqc : ContinuousOn q (Ici 0) := fun t ht => (hq' t ht).continuousWithinAt
  have hMc := M_cont.continuousOn (s := Ici 0)
  have ha0 : (0 : ℝ) ≤ 1 / 5 := by norm_num
  obtain ⟨hpa1, hpa2, hfa1, hfa2, hqa1, hqa2⟩ := ha
  refine cont_ind ?_ ?_ ?_
  · have hsub : Icc (1 / 5 : ℝ) T ⊆ Ici 0 := fun x hx => le_trans ha0 hx.1
    have h1 := hqc.mono hsub
    have h2 := hfc.mono hsub
    have h3 := hpc.mono hsub
    have h4 := hMc.mono hsub
    fun_prop
  · have hM := M_ge ha0
    simp only [lt_min_iff]
    refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith, by linarith⟩
  intro t ht H
  have Hs : ∀ s ∈ Ico (1 / 5 : ℝ) t, 0 < q s ∧ 0 < f s ∧ q s < 20 * p s ∧ f s < M s ∧
      20 * p s < M s := by
    intro s hs
    have := H s hs
    simp only [lt_min_iff] at this
    exact ⟨this.1.1, this.1.2, by linarith [this.2.1], by linarith [this.2.2.1],
      by linarith [this.2.2.2]⟩
  have hs0 : ∀ s ∈ Ioo (1 / 5 : ℝ) t, 0 < s := fun s hs => lt_trans (by norm_num) hs.1
  have hIco : ∀ s ∈ Ioo (1 / 5 : ℝ) t, s ∈ Ico (1 / 5 : ℝ) t := fun s hs => ⟨hs.1.le, hs.2⟩
  -- derivatives inside (1/5, t), every clamp inactive
  have hder : ∀ s ∈ Ioo (1 / 5 : ℝ) t, HasDerivAt f (p s) s ∧ HasDerivAt p (q s) s ∧
      HasDerivAt q (-(c * f s * q s) + β * (p s ^ 2 - 1)) s := by
    intro s hs
    obtain ⟨h1, h2, h3, h4, h5⟩ := Hs s (hIco s hs)
    have hf := (hf' s (hs0 s hs).le).hasDerivAt (Ici_mem_nhds (hs0 s hs))
    have hp := (hp' s (hs0 s hs).le).hasDerivAt (Ici_mem_nhds (hs0 s hs))
    have hq := (hq' s (hs0 s hs).le).hasDerivAt (Ici_mem_nhds (hs0 s hs))
    have ef : ecl (M s) (f s) = f s := ecl_of_abs_le (abs_le.mpr ⟨by linarith, by linarith⟩)
    have ep : ecl (M s) (p s) = p s := ecl_of_abs_le (abs_le.mpr ⟨by linarith, by linarith⟩)
    have eq : ecl (M s) (q s) = q s := ecl_of_abs_le (abs_le.mpr ⟨by linarith, by linarith⟩)
    rw [ep] at hf; rw [eq] at hp; rw [ef, eq, ep] at hq
    exact ⟨hf, hp, hq⟩
  -- (1) the velocity does not decrease; (2) nor does f
  have hP : ∀ s ∈ Icc (1 / 5 : ℝ) t, p (1 / 5) ≤ p s := by
    intro s hs
    exact le_of_deriv ha0 hs.1 hpc (fun r hr => (hder r ⟨hr.1, hr.2.trans_le hs.2⟩).2.1)
      (fun r hr => (Hs r ⟨hr.1.le, hr.2.trans_le hs.2⟩).1.le)
  have hF : ∀ s ∈ Icc (1 / 5 : ℝ) t, f (1 / 5) ≤ f s := by
    intro s hs
    exact le_of_deriv ha0 hs.1 hfc (fun r hr => (hder r ⟨hr.1, hr.2.trans_le hs.2⟩).1)
      (fun r hr => by have := hP r ⟨hr.1.le, hr.2.le.trans hs.2⟩; linarith)
  -- (3) 20 c f - β p does not decrease
  have hV : ∀ s ∈ Icc (1 / 5 : ℝ) t, 4 / 5 ≤ 20 * c * f s - β * p s := by
    intro s hs
    have := le_of_deriv (g := fun r => 20 * c * f r - β * p r)
      (g' := fun r => 20 * c * p r - β * q r) ha0 hs.1
      (((continuous_const.continuousOn).mul hfc).sub ((continuous_const.continuousOn).mul hpc))
      (fun r hr => (((hder r ⟨hr.1, hr.2.trans_le hs.2⟩).1.const_mul (20 * c)).sub
        ((hder r ⟨hr.1, hr.2.trans_le hs.2⟩).2.1.const_mul β)).congr_deriv (by ring))
      (fun r hr => by
        obtain ⟨h1, h2, h3, -, -⟩ := Hs r ⟨hr.1.le, hr.2.trans_le hs.2⟩
        have : 0 < p r := by linarith
        nlinarith)
    have e1 : 20 * f (1 / 5) ≤ 20 * c * f (1 / 5) := by nlinarith
    have e2 : β * p (1 / 5) ≤ p (1 / 5) := by nlinarith
    linarith
  -- (4) p e^{-20 s} does not increase
  have hE : ∀ r : ℝ, HasDerivAt (fun x => Real.exp (-(20 * x))) (Real.exp (-(20 * r)) * -(20 * 1)) r :=
    fun r => ((hasDerivAt_id' r).const_mul 20).neg.exp
  have hPup : ∀ s ∈ Icc (1 / 5 : ℝ) t, p s ≤ 12 / 5 * Real.exp (20 * s) := by
    intro s hs
    have := le_of_deriv (g := fun r => -(p r * Real.exp (-(20 * r))))
      (g' := fun r => (20 * p r - q r) * Real.exp (-(20 * r))) ha0 hs.1
      ((hpc.mul (by fun_prop : Continuous fun x : ℝ => Real.exp (-(20 * x))).continuousOn).neg)
      (fun r hr => (((hder r ⟨hr.1, hr.2.trans_le hs.2⟩).2.1.mul (hE r)).neg).congr_deriv
        (by ring))
      (fun r hr => by
        obtain ⟨-, -, h3, -, -⟩ := Hs r ⟨hr.1.le, hr.2.trans_le hs.2⟩
        exact mul_nonneg (by linarith) (Real.exp_pos _).le)
    have hE1 : Real.exp (-(20 * (1 / 5 : ℝ))) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    have hpa : p (1 / 5) * Real.exp (-(20 * (1 / 5 : ℝ))) ≤ 12 / 5 := by
      have := Real.exp_pos (-(20 * (1 / 5 : ℝ))); nlinarith
    have hprod : Real.exp (-(20 * s)) * Real.exp (20 * s) = 1 := by
      rw [← Real.exp_add]; simp
    have hes := Real.exp_pos (20 * s)
    have : p s * Real.exp (-(20 * s)) ≤ 12 / 5 := by linarith
    calc p s = p s * Real.exp (-(20 * s)) * Real.exp (20 * s) := by
            rw [mul_assoc, hprod, mul_one]
      _ ≤ 12 / 5 * Real.exp (20 * s) := mul_le_mul_of_nonneg_right this hes.le
  -- (5) f below 6/25 + 3/25 e^{20 s}
  have hFup : ∀ s ∈ Icc (1 / 5 : ℝ) t, f s ≤ 6 / 25 + 3 / 25 * Real.exp (20 * s) := by
    intro s hs
    have := le_of_deriv (g := fun r => 3 / 25 * Real.exp (20 * r) - f r)
      (g' := fun r => 3 / 25 * (Real.exp (20 * r) * (20 * 1)) - p r) ha0 hs.1
      ((by fun_prop : Continuous fun x : ℝ => 3 / 25 * Real.exp (20 * x)).continuousOn.sub hfc)
      (fun r hr => ((((hasDerivAt_id' r).const_mul 20).exp.const_mul (3 / 25)).sub
        (hder r ⟨hr.1, hr.2.trans_le hs.2⟩).1))
      (fun r hr => by
        have := hPup r ⟨hr.1.le, hr.2.le.trans hs.2⟩
        linarith)
    have := Real.exp_pos (20 * (1 / 5 : ℝ))
    linarith
  set F := 6 / 25 + 3 / 25 * Real.exp (20 * t) with hFdef
  have hfF : ∀ s ∈ Icc (1 / 5 : ℝ) t, 0 < f s ∧ f s ≤ F := by
    intro s hs
    refine ⟨by linarith [hF s hs], (hFup s hs).trans ?_⟩
    have := Real.exp_le_exp.mpr (by linarith [hs.2] : 20 * s ≤ 20 * t)
    linarith
  -- (6) w = 20 p - q stays positive
  have hW : 0 < 20 * p t - q t := by
    set C := 20 + 2 * F with hC
    have := le_of_deriv (g := fun r => (20 * p r - q r) * Real.exp (C * r))
      (g' := fun r => (20 * q r - (-(c * f r * q r) + β * (p r ^ 2 - 1))) * Real.exp (C * r) +
        (20 * p r - q r) * (Real.exp (C * r) * (C * 1))) ha0 ht.1.le
      (((continuous_const.continuousOn.mul hpc).sub hqc).mul
        (by fun_prop : Continuous fun x : ℝ => Real.exp (C * x)).continuousOn)
      (fun r hr => ((((hder r hr).2.1.const_mul 20).sub (hder r hr).2.2).mul
        ((hasDerivAt_id' r).const_mul C).exp))
      (fun r hr => by
        obtain ⟨h1, h2, h3, -, -⟩ := Hs r (hIco r hr)
        have hv := hV r ⟨hr.1.le, hr.2.le⟩
        have hf := hfF r ⟨hr.1.le, hr.2.le⟩
        have hp : 0 < p r := by linarith
        have key : (20 * q r - (-(c * f r * q r) + β * (p r ^ 2 - 1))) * Real.exp (C * r) +
            (20 * p r - q r) * (Real.exp (C * r) * (C * 1)) =
            (400 * p r + p r * (20 * c * f r - β * p r) + β +
              (2 * F - c * f r) * (20 * p r - q r)) * Real.exp (C * r) := by
          rw [hC]; ring
        rw [key]
        have hcf : c * f r ≤ 2 * F := by nlinarith
        refine mul_nonneg ?_ (Real.exp_pos _).le
        have := mul_nonneg hp.le (by linarith : (0 : ℝ) ≤ 20 * c * f r - β * p r)
        have := mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * F - c * f r)
          (by linarith : (0 : ℝ) ≤ 20 * p r - q r)
        linarith)
    have h0 : 0 < (20 * p (1 / 5) - q (1 / 5)) * Real.exp (C * (1 / 5)) :=
      mul_pos (by linarith) (Real.exp_pos _)
    have := lt_of_lt_of_le h0 this
    exact pos_of_mul_pos_left this (Real.exp_pos _).le
  -- (7) the shear stays positive
  have hQ : 0 < q t := by
    set D := 2 * F with hD
    have := le_of_deriv (g := fun r => q r * Real.exp (D * r))
      (g' := fun r => (-(c * f r * q r) + β * (p r ^ 2 - 1)) * Real.exp (D * r) +
        q r * (Real.exp (D * r) * (D * 1))) ha0 ht.1.le
      (hqc.mul (by fun_prop : Continuous fun x : ℝ => Real.exp (D * x)).continuousOn)
      (fun r hr => ((hder r hr).2.2.mul ((hasDerivAt_id' r).const_mul D).exp))
      (fun r hr => by
        obtain ⟨h1, h2, h3, -, -⟩ := Hs r (hIco r hr)
        have hf := hfF r ⟨hr.1.le, hr.2.le⟩
        have hp := hP r ⟨hr.1.le, hr.2.le⟩
        have key : (-(c * f r * q r) + β * (p r ^ 2 - 1)) * Real.exp (D * r) +
            q r * (Real.exp (D * r) * (D * 1)) =
            ((2 * F - c * f r) * q r + β * (p r ^ 2 - 1)) * Real.exp (D * r) := by
          rw [hD]; ring
        rw [key]
        have hcf : c * f r ≤ 2 * F := by nlinarith
        refine mul_nonneg ?_ (Real.exp_pos _).le
        have := mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * F - c * f r) h1.le
        have : 0 ≤ β * (p r ^ 2 - 1) := mul_nonneg hb0.le (by nlinarith)
        linarith)
    have h0 : 0 < q (1 / 5) * Real.exp (D * (1 / 5)) := mul_pos (by linarith) (Real.exp_pos _)
    have := lt_of_lt_of_le h0 this
    exact pos_of_mul_pos_left this (Real.exp_pos _).le
  -- (8) assemble at t
  have htI : t ∈ Icc (1 / 5 : ℝ) t := ⟨ht.1.le, le_rfl⟩
  have hft := hfF t htI
  have hpt := hPup t htI
  have hfu := hFup t htI
  have he1 := Real.one_le_exp (by linarith [ht.1] : 0 ≤ 20 * t)
  simp only [lt_min_iff]
  refine ⟨⟨hQ, hft.1⟩, hW, ?_, ?_⟩
  · unfold M; linarith
  · unfold M; linarith

/-- Every clamp is inactive at every point of [0, ∞), and the shear is positive there. -/
theorem inactive : ∀ t ∈ Ici (0 : ℝ),
    |f t| ≤ M t ∧ |p t| ≤ M t ∧ |q t| ≤ M t ∧ 0 < q t := by
  have hqc : ContinuousOn q (Ici 0) := fun t ht => (hq' t ht).continuousWithinAt
  have h1 : ∀ t ∈ Icc (0 : ℝ) (1 / 5), 0 < min (q t - 8) (12 - q t) := by
    refine cont_ind ?_ ?_ ?_
    · have h1 := hqc.mono (Icc_subset_Ici_self : Icc (0 : ℝ) (1 / 5) ⊆ Ici 0)
      fun_prop
    · rw [hq0]; norm_num
    intro t ht H
    have hq : ∀ s ∈ Ico 0 t, 8 < q s ∧ q s < 12 := fun s hs => by
      have := H s hs; simp only [lt_min_iff] at this; constructor <;> linarith [this.1, this.2]
    obtain ⟨-, hlo, hhi⟩ := phase1 hc1 hc2 hb0 hb1 f p q hf' hp' hq' hf0 hp0 hq0
      ⟨ht.1.le, ht.2⟩ hq
    simp only [lt_min_iff]
    constructor <;> linarith [ht.2]
  have hq5 : ∀ s ∈ Ico (0 : ℝ) (1 / 5), 8 < q s ∧ q s < 12 := fun s hs => by
    have := h1 s ⟨hs.1, hs.2.le⟩; simp only [lt_min_iff] at this
    constructor <;> linarith [this.1, this.2]
  obtain ⟨hB, -, -⟩ := phase1 hc1 hc2 hb0 hb1 f p q hf' hp' hq' hf0 hp0 hq0
    ⟨by norm_num, le_rfl⟩ hq5
  have hq55 := h1 (1 / 5) ⟨by norm_num, le_rfl⟩
  simp only [lt_min_iff] at hq55
  intro t ht
  rcases le_or_gt t (1 / 5) with htl | htl
  · obtain ⟨b1, b2, b3, b4⟩ := hB t ⟨ht, htl⟩
    have hqt := h1 t ⟨ht, htl⟩
    simp only [lt_min_iff] at hqt
    have hM := M_ge (show (0 : ℝ) ≤ t from ht)
    have ht0 : (0 : ℝ) ≤ t := ht
    refine ⟨abs_le.mpr ⟨by nlinarith, by nlinarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩,
      abs_le.mpr ⟨by linarith, by linarith⟩, by linarith⟩
  · obtain ⟨b1, b2, b3, b4⟩ := hB (1 / 5) ⟨by norm_num, le_rfl⟩
    have h2 := phase2 hc1 hc2 hb0 hb1 f p q hf' hp' hq'
      ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
      (T := t) t ⟨htl.le, le_rfl⟩
    simp only [lt_min_iff] at h2
    obtain ⟨⟨hq, hf⟩, hw, hMf, hMp⟩ := h2
    refine ⟨abs_le.mpr ⟨by linarith [M_pos t], by linarith⟩,
      abs_le.mpr ⟨by linarith [M_pos t], by linarith⟩,
      abs_le.mpr ⟨by linarith [M_pos t], by linarith⟩, hq⟩

end bounds

/-- For every c in [1, 2] and every β in (0, 1] there is a solution of f' = p, p' = q,
q' = −c f q + β (p² − 1) on [0, ∞) with f(0) = 0, p(0) = 0, q(0) = 10 and q positive on [0, ∞). -/
theorem exists_wall_ten {c β : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2) (hb0 : 0 < β) (hb1 : β ≤ 1) :
    ∃ f p q : ℝ → ℝ, (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(c * f η * q η) + β * (p η ^ 2 - 1)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ q 0 = 10 ∧ ∀ η ∈ Ici (0 : ℝ), 0 < q η := by
  obtain ⟨Y, hY0, hY⟩ := exists_sol (c := c) (β := β) (by linarith) hc2 hb0.le hb1
    ((0 : ℝ), (0 : ℝ), (10 : ℝ))
  have hf' : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => (Y s).1) (ecl (M t) (Y t).2.1)
      (Ici 0) t := fun t ht => (hY t ht).fst
  have hp' : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => (Y s).2.1) (ecl (M t) (Y t).2.2)
      (Ici 0) t := fun t ht => (hY t ht).snd.fst
  have hq' : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => (Y s).2.2)
      (-(c * ecl (M t) (Y t).1 * ecl (M t) (Y t).2.2) + β * (ecl (M t) (Y t).2.1 ^ 2 - 1))
      (Ici 0) t := fun t ht => (hY t ht).snd.snd
  have h0 : (Y 0).1 = 0 ∧ (Y 0).2.1 = 0 ∧ (Y 0).2.2 = 10 := by rw [hY0]; simp
  have hin := inactive hc1 hc2 hb0 hb1 (fun s => (Y s).1) (fun s => (Y s).2.1)
    (fun s => (Y s).2.2) hf' hp' hq' h0.1 h0.2.1 h0.2.2
  refine ⟨fun s => (Y s).1, fun s => (Y s).2.1, fun s => (Y s).2.2, fun t ht => ?_,
    fun t ht => ?_, fun t ht => ?_, h0.1, h0.2.1, h0.2.2, fun t ht => (hin t ht).2.2.2⟩
  · have := hf' t ht; rwa [ecl_of_abs_le (hin t ht).2.1] at this
  · have := hp' t ht; rwa [ecl_of_abs_le (hin t ht).2.2.1] at this
  · have := hq' t ht
    rwa [ecl_of_abs_le (hin t ht).1, ecl_of_abs_le (hin t ht).2.2.1,
      ecl_of_abs_le (hin t ht).2.1] at this

end Checked.Trust.ExpFlow
