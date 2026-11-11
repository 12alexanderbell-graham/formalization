import Checked.FSRev.RIdent
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Falkner–Skan adverse pressure gradient with a nonnegative scaled coefficient: global continuation of a solution that has entered the energy well around the edge value with positive stream function, through a dissipative clamped field whose energy is nonincreasing and keeps every clamp inactive. Module `RGlobal`, promoted from `Work/FSRev/RGlobal.lean`. -/

namespace Checked.FSRev.RGlobal
open Set Filter Topology Checked.FSNeg.NBase Checked.FSSep.SBase Checked.FSSep.SFlow Checked.FSRev.RIdent

/-- Clamp to [0, C]. -/
noncomputable def cp (C x : ℝ) : ℝ := max 0 (min C x)

theorem cp_sub (C x y : ℝ) : |cp C x - cp C y| ≤ |x - y| := by
  unfold cp
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le (by simp) ?_)
  exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le (by simp) le_rfl)

theorem cp_nonneg (C x : ℝ) : 0 ≤ cp C x := le_max_left _ _

theorem abs_cp_le {C : ℝ} (hC : 0 ≤ C) (x : ℝ) : |cp C x| ≤ C :=
  abs_le.2 ⟨by linarith [cp_nonneg C x], max_le hC (min_le_left _ _)⟩

theorem cp_eq {C x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ C) : cp C x = x := by
  unfold cp; rw [min_eq_right h1, max_eq_right h0]

/-- The dissipative clamped field of the tail (time s ≥ 0 counted from the start of the tail). -/
noncomputable def vT (K s : ℝ) (y : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (cl 2 y.2.1, cl 2 y.2.2, -(K * cp (2 * max s 0 + 4) y.1 * cl 2 y.2.2) + 1 - cl 2 y.2.1 ^ 2)

theorem lip (K : ℝ) {T t : ℝ} (ht : t ∈ Icc 0 T) :
    LipschitzWith (Real.toNNReal (2 * |K| * T + 6 * |K| + 4)) (vT K t) := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  refine LipschitzWith.of_dist_le_mul fun y z => ?_
  have hK0 : 0 ≤ |K| := abs_nonneg K
  rw [Real.coe_toNNReal _ (by positivity)]
  simp only [vT, Prod.dist_eq, Real.dist_eq]
  set m := max |y.1 - z.1| (max |y.2.1 - z.2.1| |y.2.2 - z.2.2|)
  have hd1 : |y.1 - z.1| ≤ m := le_max_left _ _
  have hd2 : |y.2.1 - z.2.1| ≤ m := (le_max_left _ _).trans (le_max_right _ _)
  have hd3 : |y.2.2 - z.2.2| ≤ m := (le_max_right _ _).trans (le_max_right _ _)
  have hm : 0 ≤ m := (abs_nonneg _).trans hd1
  set C := 2 * max t 0 + 4 with hC
  have hC0 : 0 ≤ C := by positivity
  have hCT : C ≤ 2 * T + 4 := by
    have : max t 0 ≤ T := max_le ht.2 hT
    linarith
  refine max_le ?_ (max_le ?_ ?_)
  · have := cl_sub 2 y.2.1 z.2.1; nlinarith [mul_nonneg hK0 hT, mul_nonneg (mul_nonneg hK0 hT) hm, mul_nonneg hK0 hm]
  · have := cl_sub 2 y.2.2 z.2.2; nlinarith [mul_nonneg hK0 hT, mul_nonneg (mul_nonneg hK0 hT) hm, mul_nonneg hK0 hm]
  · set a := cp C y.1
    set a' := cp C z.1
    set b := cl 2 y.2.2
    set b' := cl 2 z.2.2
    set c := cl 2 y.2.1
    set c' := cl 2 z.2.1
    have ha : |a - a'| ≤ |y.1 - z.1| := cp_sub C y.1 z.1
    have hb : |b - b'| ≤ |y.2.2 - z.2.2| := cl_sub 2 y.2.2 z.2.2
    have hc : |c - c'| ≤ |y.2.1 - z.2.1| := cl_sub 2 y.2.1 z.2.1
    have hbb : |b| ≤ 2 := abs_cl_le (by norm_num) _
    have haa : |a'| ≤ C := abs_cp_le hC0 _
    have hcc : |c| ≤ 2 := abs_cl_le (by norm_num) _
    have hcc' : |c'| ≤ 2 := abs_cl_le (by norm_num) _
    have e : -(K * a * b) + 1 - c ^ 2 - (-(K * a' * b') + 1 - c' ^ 2)
        = -(K * ((a - a') * b + a' * (b - b'))) + (c + c') * (c' - c) := by ring
    rw [abs_sub_comm] at hc
    rw [e]
    have h1 : |(a - a') * b| ≤ 2 * m := by
      rw [abs_mul, mul_comm]
      exact mul_le_mul hbb (ha.trans hd1) (abs_nonneg _) (by norm_num)
    have h2 : |a' * (b - b')| ≤ C * m := by
      rw [abs_mul]
      exact mul_le_mul haa (hb.trans hd3) (abs_nonneg _) hC0
    have h4 : |(c + c') * (c' - c)| ≤ 4 * m := by
      rw [abs_mul]
      have : |c + c'| ≤ 4 := (abs_add_le c c').trans (by linarith)
      exact mul_le_mul this (hc.trans hd2) (abs_nonneg _) (by norm_num)
    have h3 := abs_add_le ((a - a') * b) (a' * (b - b'))
    have h5 := abs_add_le (-(K * ((a - a') * b + a' * (b - b')))) ((c + c') * (c' - c))
    rw [abs_neg, abs_mul] at h5
    have h6 : |(a - a') * b + a' * (b - b')| ≤ (2 * T + 6) * m := by nlinarith
    have h7 : |K| * |(a - a') * b + a' * (b - b')| ≤ |K| * ((2 * T + 6) * m) :=
      mul_le_mul_of_nonneg_left h6 hK0
    nlinarith [mul_nonneg hK0 hm]

theorem norm_le (K : ℝ) {T t : ℝ} (ht : t ∈ Icc 0 T) (y : ℝ × ℝ × ℝ) :
    ‖vT K t y‖ ≤ 4 * |K| * T + 8 * |K| + 5 := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  simp only [vT, Prod.norm_def, Real.norm_eq_abs]
  set C := 2 * max t 0 + 4 with hC
  have hC0 : 0 ≤ C := by positivity
  have hCT : C ≤ 2 * T + 4 := by
    have : max t 0 ≤ T := max_le ht.2 hT
    linarith
  have h1 := abs_cl_le (by norm_num : (0 : ℝ) ≤ 2) y.2.1
  have h2 := abs_cl_le (by norm_num : (0 : ℝ) ≤ 2) y.2.2
  have h3 := abs_cp_le hC0 y.1
  have hK0 : 0 ≤ |K| := abs_nonneg K
  have hKT : 0 ≤ |K| * T := mul_nonneg hK0 hT
  refine max_le (by linarith) (max_le (by linarith) ?_)
  have hab : |K * cp C y.1 * cl 2 y.2.2| ≤ |K| * (C * 2) := by
    rw [abs_mul, abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul h3 h2 (abs_nonneg _) hC0) hK0
  have hab2 : |K| * (C * 2) ≤ |K| * ((2 * T + 4) * 2) := mul_le_mul_of_nonneg_left (by linarith) hK0
  have hsq : |cl 2 y.2.1 ^ 2| ≤ 4 := by
    rw [abs_pow]; nlinarith [abs_nonneg (cl 2 y.2.1)]
  have k1 := abs_sub (-(K * cp C y.1 * cl 2 y.2.2) + 1) (cl 2 y.2.1 ^ 2)
  have k2 := abs_add_le (-(K * cp C y.1 * cl 2 y.2.2)) 1
  rw [abs_neg] at k2
  simp only [abs_one] at k2
  nlinarith

theorem cont (K : ℝ) (y : ℝ × ℝ × ℝ) : Continuous (fun t => vT K t y) := by
  unfold vT cl cp
  fun_prop

theorem local_sol (K : ℝ) (y₀ : ℝ × ℝ × ℝ) {T : ℝ} (hT : 0 < T) : ∃ Y : ℝ → ℝ × ℝ × ℝ, Y 0 = y₀ ∧
    ∀ t ∈ Icc 0 T, HasDerivWithinAt Y (vT K t (Y t)) (Icc 0 T) t := by
  set L : ℝ := 4 * |K| * T + 8 * |K| + 5 with hL
  have hL0 : 0 ≤ L := by positivity
  have hPL : IsPicardLindelof (vT K) (tmin := 0) (tmax := T) ⟨0, le_rfl, hT.le⟩
      y₀ (Real.toNNReal (L * T)) 0 (Real.toNNReal L)
      (Real.toNNReal (2 * |K| * T + 6 * |K| + 4)) :=
    { lipschitzOnWith := fun t ht => (lip K ht).lipschitzOnWith
      continuousOn := fun x _ => (cont K x).continuousOn
      norm_le := fun t ht p _ => by
        rw [Real.coe_toNNReal _ hL0]; exact norm_le K ht p
      mul_max_le := by
        rw [Real.coe_toNNReal _ hL0, Real.coe_toNNReal _ (by positivity)]
        simp only [NNReal.coe_zero, sub_zero, sub_self]
        rw [max_eq_left hT.le] }
  exact hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

theorem unique_right {K T : ℝ} (hT : 0 ≤ T) {Y Z : ℝ → ℝ × ℝ × ℝ}
    (hY : ∀ t ∈ Icc 0 T, HasDerivWithinAt Y (vT K t (Y t)) (Icc 0 T) t)
    (hZ : ∀ t ∈ Icc 0 T, HasDerivWithinAt Z (vT K t (Z t)) (Icc 0 T) t)
    (h0 : Y 0 = Z 0) : EqOn Y Z (Icc 0 T) := by
  refine ODE_solution_unique_of_mem_Icc_right (v := vT K) (s := fun _ => univ)
    (K := Real.toNNReal (2 * |K| * T + 6 * |K| + 4))
    (fun t ht => (lip K (Ico_subset_Icc_self ht)).lipschitzOnWith)
    (fun t ht => (hY t ht).continuousWithinAt) (fun t ht => ?_) (fun _ _ => mem_univ _)
    (fun t ht => (hZ t ht).continuousWithinAt) (fun t ht => ?_) (fun _ _ => mem_univ _) h0
  · have hmem : t ∈ Icc 0 T := ⟨ht.1, ht.2.le⟩
    refine (hY t hmem).mono_of_mem_nhdsWithin ?_
    exact Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)
  · have hmem : t ∈ Icc 0 T := ⟨ht.1, ht.2.le⟩
    refine (hZ t hmem).mono_of_mem_nhdsWithin ?_
    exact Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)

theorem exists_sol (K : ℝ) (y₀ : ℝ × ℝ × ℝ) : ∃ Y : ℝ → ℝ × ℝ × ℝ, Y 0 = y₀ ∧
    ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt Y (vT K t (Y t)) (Ici 0) t := by
  have hex : ∀ n : ℕ, ∃ Y : ℝ → ℝ × ℝ × ℝ, Y 0 = y₀ ∧
      ∀ t ∈ Icc 0 ((n : ℝ) + 1), HasDerivWithinAt Y (vT K t (Y t)) (Icc 0 ((n : ℝ) + 1)) t :=
    fun n => local_sol K y₀ (by positivity)
  choose sol hsol0 hsol using hex
  have hag : ∀ k n : ℕ, ∀ s ∈ Icc (0 : ℝ) ((k : ℝ) + 1), s ≤ (n : ℝ) + 1 → sol k s = sol n s := by
    intro k n s hs hsn
    rcases le_total k n with hkn | hnk
    · have hkn' : (k : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hkn 1
      exact unique_right (by positivity) (hsol k)
        (fun t ht => (hsol n t ⟨ht.1, ht.2.trans hkn'⟩).mono (Icc_subset_Icc_right hkn'))
        ((hsol0 k).trans (hsol0 n).symm) hs
    · have hnk' : (n : ℝ) + 1 ≤ (k : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hnk 1
      exact (unique_right (by positivity) (hsol n)
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


/-- The flow of the tail field from y₀. -/
noncomputable def flowT (K : ℝ) (y₀ : ℝ × ℝ × ℝ) : ℝ → ℝ × ℝ × ℝ := Classical.choose (exists_sol K y₀)

theorem flowT_zero (K : ℝ) (y₀ : ℝ × ℝ × ℝ) : flowT K y₀ 0 = y₀ := (Classical.choose_spec (exists_sol K y₀)).1

theorem flowT_deriv (K : ℝ) (y₀ : ℝ × ℝ × ℝ) :
    ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (flowT K y₀) (vT K t (flowT K y₀ t)) (Ici 0) t :=
  (Classical.choose_spec (exists_sol K y₀)).2

theorem cl_cont : Continuous (cl 2) := by unfold cl; fun_prop

/-- Kinetic part of the energy: Q' = clamp of q. -/
noncomputable def Q (x : ℝ) : ℝ := ∫ r in (0 : ℝ)..x, cl 2 r

/-- Potential part of the energy: W' = (clamp of p)² − 1, W(1) = 0. -/
noncomputable def W (x : ℝ) : ℝ := ∫ r in (1 : ℝ)..x, (cl 2 r ^ 2 - 1)

theorem hasDerivAt_Q (x : ℝ) : HasDerivAt Q (cl 2 x) x :=
  (cl_cont.integral_hasStrictDerivAt 0 x).hasDerivAt

theorem hasDerivAt_W (x : ℝ) : HasDerivAt W (cl 2 x ^ 2 - 1) x :=
  (((cl_cont.pow 2).sub continuous_const).integral_hasStrictDerivAt 1 x).hasDerivAt

theorem cl_le_of_mem {a b r : ℝ} (ha : |a| ≤ 2) (hb : |b| ≤ 2) (hr : r ∈ uIcc a b) : cl 2 r = r := by
  apply cl_of_abs_le
  rw [mem_uIcc] at hr
  rw [abs_le] at ha hb ⊢
  rcases hr with h | h <;> constructor <;> linarith [h.1, h.2]

theorem Q_eq {x : ℝ} (hx : |x| ≤ 2) : Q x = x ^ 2 / 2 := by
  have : Q x = ∫ r in (0 : ℝ)..x, r := by
    unfold Q
    exact intervalIntegral.integral_congr fun r hr => cl_le_of_mem (by norm_num) hx hr
  rw [this, integral_id]; ring

theorem W_eq {x : ℝ} (hx : |x| ≤ 2) : W x = (x - 1) ^ 2 * (x + 2) / 3 := by
  have : W x = ∫ r in (1 : ℝ)..x, (r ^ 2 - 1) := by
    unfold W
    exact intervalIntegral.integral_congr fun r hr => by
      rw [cl_le_of_mem (by norm_num) hx hr]
  rw [this, intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
    intervalIntegrable_const, integral_pow, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem Q_nonneg (x : ℝ) : 0 ≤ Q x := by
  rcases le_total 0 x with h | h
  · exact intervalIntegral.integral_nonneg h fun u hu => le_max_of_le_right (le_min (by norm_num) hu.1)
  · unfold Q
    rw [intervalIntegral.integral_symm, ← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_nonneg h fun u hu =>
      neg_nonneg.2 (max_le (by norm_num) ((min_le_right _ _).trans hu.2))

/-- Global continuation: a solution of the tail field that starts with 0 < f ≤ 4, |p − 1| ≤ 1/2 and
|q| ≤ 1/2 keeps 0 < p < 2, |q| < 2 and 0 < f ≤ 2s + 4, so it solves the unclamped field on [0, ∞). -/
theorem tail {K : ℝ} (hK : 0 ≤ K) {Z : ℝ → ℝ × ℝ × ℝ}
    (hZ : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt Z (vT K s (Z s)) (Ici 0) s)
    (hf0 : 0 < (Z 0).1) (hf4 : (Z 0).1 ≤ 4) (hp0 : |(Z 0).2.1 - 1| ≤ 1 / 2) (hq0 : |(Z 0).2.2| ≤ 1 / 2) :
    ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt Z (uS K (Z s)) (Ici 0) s := by
  set f : ℝ → ℝ := fun s => (Z s).1 with hfd
  set p : ℝ → ℝ := fun s => (Z s).2.1 with hpd
  set q : ℝ → ℝ := fun s => (Z s).2.2 with hqd
  have hf' : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt f (cl 2 (p s)) (Ici 0) s := fun s hs => (hZ s hs).fst
  have hp' : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt p (cl 2 (q s)) (Ici 0) s := fun s hs => (hZ s hs).snd.fst
  have hq' : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt q
      (-(K * cp (2 * max s 0 + 4) (f s) * cl 2 (q s)) + 1 - cl 2 (p s) ^ 2) (Ici 0) s :=
    fun s hs => (hZ s hs).snd.snd
  have hpc : ContinuousOn p (Ici 0) := fun s hs => (hp' s hs).continuousWithinAt
  have hqc : ContinuousOn q (Ici 0) := fun s hs => (hq' s hs).continuousWithinAt
  set E : ℝ → ℝ := fun s => Q (q s) + W (p s) with hEd
  have hE' : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt E
      (-(K * cp (2 * max s 0 + 4) (f s) * cl 2 (q s) ^ 2)) (Ici 0) s := by
    intro s hs
    have h := ((hasDerivAt_Q (q s)).comp_hasDerivWithinAt s (hq' s hs)).add
      ((hasDerivAt_W (p s)).comp_hasDerivWithinAt s (hp' s hs))
    exact h.congr_deriv (by ring)
  have hEanti : AntitoneOn E (Ici 0) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
      (f' := fun s => -(K * cp (2 * max s 0 + 4) (f s) * cl 2 (q s) ^ 2))
      (fun s hs => (hE' s hs).continuousWithinAt) (fun s hs => ?_) (fun s hs => ?_)
    · exact (hE' s (interior_subset hs)).mono interior_subset
    · exact neg_nonpos.2 (mul_nonneg (mul_nonneg hK (cp_nonneg _ _)) (sq_nonneg _))
  have hE0 : E 0 < 1 / 2 := by
    have a1 := abs_le.1 hp0
    have a2 := abs_le.1 hq0
    simp only [hEd]
    rw [Q_eq (abs_le.2 ⟨by linarith, by linarith⟩), W_eq (abs_le.2 ⟨by linarith, by linarith⟩)]
    have hq2 : q 0 ^ 2 ≤ 1 / 4 := by nlinarith
    have hp2 : (p 0 - 1) ^ 2 ≤ 1 / 4 := by nlinarith
    have h3 : (p 0 - 1) ^ 2 * (p 0 + 2) ≤ 1 / 4 * (7 / 2) :=
      mul_le_mul hp2 (by linarith) (by linarith) (by norm_num)
    linarith
  have hEle : ∀ s ∈ Ici (0 : ℝ), E s < 1 / 2 := fun s hs =>
    (hEanti ((mem_Ici.2 le_rfl)) hs hs).trans_lt hE0
  have hpos : ∀ s ∈ Ici (0 : ℝ), 0 < p s := by
    intro s hs
    by_contra h
    push Not at h
    obtain ⟨s', hs', e⟩ := intermediate_value_Icc' (show (0 : ℝ) ≤ s from hs) (hpc.mono Icc_subset_Ici_self)
      ⟨h, by linarith [(abs_le.1 hp0).1]⟩
    have := hEle s' hs'.1
    simp only [hEd] at this
    rw [e, W_eq (by norm_num)] at this
    norm_num at this
    linarith [Q_nonneg (q s')]
  have hlt2 : ∀ s ∈ Ici (0 : ℝ), p s < 2 := by
    intro s hs
    by_contra h
    push Not at h
    obtain ⟨s', hs', e⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ s from hs) (hpc.mono Icc_subset_Ici_self)
      ⟨by linarith [(abs_le.1 hp0).2], h⟩
    have := hEle s' hs'.1
    simp only [hEd] at this
    rw [e, W_eq (by norm_num)] at this
    norm_num at this
    linarith [Q_nonneg (q s')]
  have hW : ∀ s ∈ Ici (0 : ℝ), 0 ≤ W (p s) := by
    intro s hs
    have h1 := hpos s hs
    have h2 := hlt2 s hs
    rw [W_eq (abs_le.2 ⟨by linarith, by linarith⟩)]
    positivity
  have hqb : ∀ s ∈ Ici (0 : ℝ), |q s| < 2 := by
    intro s hs
    by_contra h
    push Not at h
    rcases le_abs'.1 h with h | h
    · obtain ⟨s', hs', e⟩ := intermediate_value_Icc' (show (0 : ℝ) ≤ s from hs) (hqc.mono Icc_subset_Ici_self)
        ⟨h, by linarith [(abs_le.1 hq0).1]⟩
      have := hEle s' hs'.1
      simp only [hEd] at this
      rw [e, Q_eq (by norm_num)] at this
      linarith [hW s' hs'.1]
    · obtain ⟨s', hs', e⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ s from hs) (hqc.mono Icc_subset_Ici_self)
        ⟨by linarith [(abs_le.1 hq0).2], h⟩
      have := hEle s' hs'.1
      simp only [hEd] at this
      rw [e, Q_eq (by norm_num)] at this
      linarith [hW s' hs'.1]
  have hclp : ∀ s ∈ Ici (0 : ℝ), cl 2 (p s) = p s := fun s hs =>
    cl_of_abs_le (abs_le.2 ⟨by linarith [hpos s hs], (hlt2 s hs).le⟩)
  have hfmono : MonotoneOn f (Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) (f' := fun s => cl 2 (p s))
      (fun s hs => (hf' s hs).continuousWithinAt) (fun s hs => ?_) (fun s hs => ?_)
    · exact (hf' s (interior_subset hs)).mono interior_subset
    · rw [hclp s (interior_subset hs)]; exact (hpos s (interior_subset hs)).le
  have hg' : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => f s - 2 * s) (cl 2 (p s) - 2) (Ici 0) s := by
    intro s hs
    exact ((hf' s hs).sub ((hasDerivWithinAt_id s (Ici 0)).const_mul 2)).congr_deriv (by ring)
  have hganti : AntitoneOn (fun s => f s - 2 * s) (Ici 0) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0) (f' := fun s => cl 2 (p s) - 2)
      (fun s hs => (hg' s hs).continuousWithinAt) (fun s hs => ?_) (fun s hs => ?_)
    · exact (hg' s (interior_subset hs)).mono interior_subset
    · linarith [(abs_le.1 (abs_cl_le (by norm_num : (0 : ℝ) ≤ 2) (p s))).2]
  intro s hs
  have hs0 : (0 : ℝ) ≤ s := hs
  have hf1 : f 0 ≤ f s := hfmono (mem_Ici.2 le_rfl) hs hs0
  have hf2 : f s - 2 * s ≤ f 0 - 2 * 0 := hganti (mem_Ici.2 le_rfl) hs hs0
  have e : vT K s (Z s) = uS K (Z s) := by
    simp only [vT, uS, max_eq_left hs0]
    rw [cp_eq (C := 2 * s + 4) (x := f s) (by linarith) (by linarith),
      cl_of_abs_le (abs_le.2 ⟨by linarith [hpos s hs], (hlt2 s hs).le⟩), cl_of_abs_le (hqb s hs).le]
  rw [← e]
  exact hZ s hs

end Checked.FSRev.RGlobal
