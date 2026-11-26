import Work.Quantum.RadialAssemble
/-!
# H₂⁺ route step 2, completed: the global radial solution on (−1/4, ∞), continuous in k (run 2026-11-26T2228Z)

Route of `runs/2026-11-26T1628Z/README.md`, step 2. The flows of `RadialAssemble.radial_flow` for the horizons
n + 3 (n ∈ ℕ) agree where both are defined (`unique_on`: uniqueness for the linear system, Lipschitz with
constant NB(T) on [2, T]); the solution past ξ = 2 is the flow of horizon ⌈ξ⌉₊ + 3 at ξ (`glob`), and it is glued at
ξ = 2 to the Frobenius solution of `RadialStart` (equal value and equal (ξ² − 1)L′ there).

`radial_global`: along a continuous A(k) ∈ [0, 3] there are L(k, ·), L′(k, ·) with L(k, 1) = 1 and, for every
ξ > −1/4, L′ = dL/dξ and ((ξ² − 1)L′)′ = −(4ξ − kξ² + A(k))L — the radial equation of the frozen statement on all
of ξ > 1 — and for every fixed ξ, L(k, ξ) and L′(k, ξ) are continuous in k on [k₁, k₂]. No numerics.
-/

namespace Work.Quantum.RadialGlobal
open Set Filter Topology
open Work.Quantum.RadialStart Work.Quantum.RadialFlow Work.Quantum.RadialAssemble

/-- The unclamped radial system in (L, P), P = (ξ² − 1)L′. -/
noncomputable def vf (k A t : ℝ) (x : ℝ × ℝ) : ℝ × ℝ := (x.2 / (t ^ 2 - 1), -((4 * t - k * t ^ 2 + A) * x.1))

theorem lip_vf {k A T t : ℝ} (hk : |k| ≤ 3) (hA : |A| ≤ 3) (ht : t ∈ Icc 2 T) :
    LipschitzWith (Real.toNNReal (NB T)) (vf k A t) := by
  have hT : 2 ≤ T := ht.1.trans ht.2
  have hNB := NB_ge hT
  have h3 := sq_sub_one_ge ht
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.coe_toNNReal _ (by linarith)]
  simp only [vf, Prod.dist_eq, Real.dist_eq]
  have d1 : |x.1 - y.1| ≤ max |x.1 - y.1| |x.2 - y.2| := le_max_left _ _
  have d2 : |x.2 - y.2| ≤ max |x.1 - y.1| |x.2 - y.2| := le_max_right _ _
  refine max_le ?_ ?_
  · rw [← _root_.sub_div, abs_div, abs_of_pos (show (0 : ℝ) < t ^ 2 - 1 by linarith),
      div_le_iff₀ (show (0 : ℝ) < t ^ 2 - 1 by linarith)]
    have h69 : 1 ≤ NB T * (t ^ 2 - 1) := by nlinarith
    have hm0 : 0 ≤ max |x.1 - y.1| |x.2 - y.2| := (abs_nonneg _).trans d1
    have := mul_le_mul_of_nonneg_left h69 hm0
    linarith
  · have e : -((4 * t - k * t ^ 2 + A) * x.1) - -((4 * t - k * t ^ 2 + A) * y.1)
        = -((4 * t - k * t ^ 2 + A) * (x.1 - y.1)) := by ring
    rw [e, abs_neg, abs_mul]
    exact mul_le_mul (coef_bound ht hk hA) d1 (abs_nonneg _) (by linarith)

/-- Uniqueness for the linear system on [2, T]. -/
theorem unique_on {k A T : ℝ} (hk : |k| ≤ 3) (hA : |A| ≤ 3) {f g : ℝ → ℝ × ℝ}
    (hf : ∀ t ∈ Icc (2 : ℝ) T, HasDerivWithinAt f (vf k A t (f t)) (Icc 2 T) t)
    (hg : ∀ t ∈ Icc (2 : ℝ) T, HasDerivWithinAt g (vf k A t (g t)) (Icc 2 T) t) (h2 : f 2 = g 2) :
    EqOn f g (Icc 2 T) := by
  refine ODE_solution_unique_of_mem_Icc_right (v := vf k A) (s := fun _ => univ) (K := Real.toNNReal (NB T))
    (fun t ht => (lip_vf hk hA (Ico_subset_Icc_self ht)).lipschitzOnWith)
    (fun t ht => (hf t ht).continuousWithinAt) (fun t ht => ?_) (fun _ _ => mem_univ _)
    (fun t ht => (hg t ht).continuousWithinAt) (fun t ht => ?_) (fun _ _ => mem_univ _) h2
  · exact (hf t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1))
  · exact (hg t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1))

/-- From a family of solutions on [2, n + 3] with a common start, one solution on [2, ∞). -/
theorem glue_family {k A : ℝ} (hk : |k| ≤ 3) (hA : |A| ≤ 3) {x0 : ℝ × ℝ} (s : ℕ → ℝ → ℝ × ℝ)
    (h2 : ∀ n, s n 2 = x0)
    (hs : ∀ n : ℕ, ∀ t ∈ Icc (2 : ℝ) ((n : ℝ) + 3), HasDerivWithinAt (s n) (vf k A t (s n t)) (Icc 2 ((n : ℝ) + 3)) t) :
    (∀ n m : ℕ, ∀ t ∈ Icc (2 : ℝ) (n + 3), t ≤ m + 3 → s n t = s m t) ∧
    (∀ t, 2 < t → HasDerivAt (fun y => s ⌈y⌉₊ y) (vf k A t (s ⌈t⌉₊ t)) t) ∧
    HasDerivWithinAt (fun y => s ⌈y⌉₊ y) (vf k A 2 (s ⌈(2 : ℝ)⌉₊ 2)) (Ici 2) 2 := by
  -- consistency
  have cons : ∀ n m : ℕ, ∀ t ∈ Icc (2 : ℝ) (n + 3), t ≤ m + 3 → s n t = s m t := by
    intro n m t ht htm
    set T := min ((n : ℝ) + 3) ((m : ℝ) + 3)
    have hTn : T ≤ (n : ℝ) + 3 := min_le_left _ _
    have hTm : T ≤ (m : ℝ) + 3 := min_le_right _ _
    have htT : t ∈ Icc (2 : ℝ) T := ⟨ht.1, le_min ht.2 htm⟩
    refine unique_on (T := T) hk hA (fun u hu => ?_) (fun u hu => ?_) ((h2 n).trans (h2 m).symm) htT
    · exact (hs n u ⟨hu.1, hu.2.trans hTn⟩).mono (Icc_subset_Icc_right hTn)
    · exact (hs m u ⟨hu.1, hu.2.trans hTm⟩).mono (Icc_subset_Icc_right hTm)
  refine ⟨cons, fun t ht => ?_, ?_⟩
  · set n := ⌈t⌉₊
    have htn : t ≤ (n : ℝ) := Nat.le_ceil t
    have hmem : Icc (2 : ℝ) (n + 3) ∈ 𝓝 t := Icc_mem_nhds ht (by linarith)
    have hd := (hs n t ⟨ht.le, by linarith⟩).hasDerivAt hmem
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [hmem] with y hy
    -- s ⌈y⌉₊ y = s n y
    have hy' : y ≤ (⌈y⌉₊ : ℝ) + 3 := by linarith [Nat.le_ceil y]
    exact (cons n ⌈y⌉₊ y hy hy').symm
  · have hmem : Icc (2 : ℝ) ((0 : ℕ) + 3) ∈ 𝓝[Ici 2] (2 : ℝ) := by
      push_cast; exact Icc_mem_nhdsGE (by norm_num)
    have h0 := hs 0 2 ⟨le_rfl, by push_cast; norm_num⟩
    have hd := h0.mono_of_mem_nhdsWithin hmem
    have e2 : s ⌈(2 : ℝ)⌉₊ 2 = s 0 2 := by rw [h2, h2]
    rw [e2]
    refine hd.congr_of_eventuallyEq ?_ e2
    filter_upwards [hmem] with y hy
    have hy' : y ≤ (⌈y⌉₊ : ℝ) + 3 := by linarith [Nat.le_ceil y]
    exact (cons 0 ⌈y⌉₊ y hy hy').symm

/-- **Route step 2.** The global radial solution, continuous in k at every fixed ξ. -/
theorem radial_global {k₁ k₂ : ℝ} (hk₁ : 0 ≤ k₁) (hk₂ : k₂ ≤ 3) {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc k₁ k₂)) (hR3 : ∀ k ∈ Icc k₁ k₂, R k ∈ Icc (0 : ℝ) 3) :
    ∃ L L' : ℝ → ℝ → ℝ, (∀ k ∈ Icc k₁ k₂, L k 1 = 1 ∧ ∀ x, -(1 / 4 : ℝ) < x →
        HasDerivAt (L k) (L' k x) x ∧
        HasDerivAt (fun y => (y ^ 2 - 1) * L' k y) (-((4 * x - k * x ^ 2 + R k) * L k x)) x) ∧
      (∀ x, -(1 / 4 : ℝ) < x →
        ContinuousOn (fun k => L k x) (Icc k₁ k₂) ∧ ContinuousOn (fun k => L' k x) (Icc k₁ k₂)) ∧
      ∀ B, 2 ≤ B → ContinuousOn (fun z : ℝ × ℝ => L z.1 z.2) (Icc k₁ k₂ ×ˢ Icc 1 B) := by
  -- one flow per horizon n + 3
  have hfl : ∀ n : ℕ, ∃ α : E → ℝ → E, (∀ k ∈ Icc k₁ k₂, α (p0 R k) 2 = p0 R k ∧
      (∀ t ∈ Icc (2 : ℝ) ((n : ℝ) + 3),
        HasDerivWithinAt (fun s => (α (p0 R k) s).1) ((α (p0 R k) t).2.1 / (t ^ 2 - 1)) (Icc 2 ((n : ℝ) + 3)) t ∧
        HasDerivWithinAt (fun s => (α (p0 R k) s).2.1)
          (-((4 * t - k * t ^ 2 + R k) * (α (p0 R k) t).1)) (Icc 2 ((n : ℝ) + 3)) t)) ∧
      (∀ t ∈ Icc (2 : ℝ) ((n : ℝ) + 3), ContinuousOn (fun k => α (p0 R k) t) (Icc k₁ k₂)) ∧
      ContinuousOn (fun z : ℝ × ℝ => α (p0 R z.1) z.2) (Icc k₁ k₂ ×ˢ Icc 2 ((n : ℝ) + 3)) :=
    fun n => radial_flow hk₁ hk₂ (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith) hR hR3
  choose α hα using hfl
  -- the pair (L, P) of flow n
  set s : ℝ → ℕ → ℝ → ℝ × ℝ := fun k n t => ((α n (p0 R k) t).1, (α n (p0 R k) t).2.1) with hsdef
  -- the global pieces
  let Lg : ℝ → ℝ → ℝ := fun k x => if x ≤ 2 then RL k (R k) (x - 1) else (s k ⌈x⌉₊ x).1
  let Pg : ℝ → ℝ → ℝ := fun k x => if x ≤ 2 then (x ^ 2 - 1) * RLd k (R k) (x - 1) else (s k ⌈x⌉₊ x).2
  let L'g : ℝ → ℝ → ℝ := fun k x => if x ≤ 2 then RLd k (R k) (x - 1) else (s k ⌈x⌉₊ x).2 / (x ^ 2 - 1)
  refine ⟨Lg, L'g, fun k hk => ?_, fun x hxq => ?_, fun B hB => ?_⟩
  · have hk3 : |k| ≤ 3 := abs_le.mpr ⟨by linarith [hk.1], by linarith [hk.2]⟩
    have hA3 : |R k| ≤ 3 := abs_le.mpr ⟨by linarith [(hR3 k hk).1], (hR3 k hk).2⟩
    have hkI : k ∈ Icc (0 : ℝ) 3 := ⟨by linarith [hk.1], by linarith [hk.2]⟩
    -- each s k n solves the system on [2, n + 3] from p0
    have hsn : ∀ n : ℕ, ∀ t ∈ Icc (2 : ℝ) ((n : ℝ) + 3),
        HasDerivWithinAt (s k n) (vf k (R k) t (s k n t)) (Icc 2 ((n : ℝ) + 3)) t := by
      intro n t ht
      obtain ⟨h1, h2⟩ := (hα n).1 k hk |>.2 t ht
      exact h1.prodMk h2
    have hs2 : ∀ n, s k n 2 = (RL k (R k) 1, 3 * RLd k (R k) 1) := by
      intro n
      have e := ((hα n).1 k hk).1
      simp only [hsdef]
      rw [e]
      simp only [p0]
    obtain ⟨cons, hder, hder2⟩ := glue_family hk3 hA3 (s k) hs2 hsn
    -- the value and P agree at 2
    have hc2 : ⌈(2 : ℝ)⌉₊ = 2 := by norm_num
    have hS2 : s k ⌈(2 : ℝ)⌉₊ 2 = (RL k (R k) 1, 3 * RLd k (R k) 1) := hs2 _
    -- Frobenius piece in ξ
    have hfro : ∀ x ∈ Ioo (-(1 / 4 : ℝ)) (9 / 4), HasDerivAt (fun y => RL k (R k) (y - 1)) (RLd k (R k) (x - 1)) x ∧
        HasDerivAt (fun y => (y ^ 2 - 1) * RLd k (R k) (y - 1))
          (-((4 * x - k * x ^ 2 + R k) * RL k (R k) (x - 1))) x := fun x hx => radial_ode hkI (hR3 k hk) hx
    -- P = (x² − 1) L′ everywhere
    have hPL : ∀ y, Pg k y = (y ^ 2 - 1) * L'g k y := by
      intro y
      by_cases hy : y ≤ 2
      · simp only [Pg, L'g, if_pos hy]
      · simp only [Pg, L'g, if_neg hy]
        have : y ^ 2 - 1 ≠ 0 := by push Not at hy; nlinarith
        field_simp
    refine ⟨?_, fun x hx => ?_⟩
    · simp only [Lg, if_pos (by norm_num : (1 : ℝ) ≤ 2), sub_self]
      exact RL_one k (R k)
    -- the derivative of (L, P) as a pair, case by case
    have key : HasDerivAt (fun y => (Lg k y, Pg k y)) (L'g k x, -((4 * x - k * x ^ 2 + R k) * Lg k x)) x := by
      rcases lt_trichotomy x 2 with hx2 | hx2 | hx2
      · -- Frobenius side, an open neighbourhood inside x < 2
        have hmem : Iio (2 : ℝ) ∈ 𝓝 x := Iio_mem_nhds hx2
        obtain ⟨d1, d2⟩ := hfro x ⟨hx, by linarith⟩
        have hd := d1.prodMk d2
        refine (hd.congr_of_eventuallyEq ?_).congr_deriv ?_
        · filter_upwards [hmem] with y hy
          simp only [Lg, Pg, if_pos (le_of_lt (show y < 2 from hy))]
        · simp only [Lg, L'g, if_pos hx2.le]
      · -- at ξ = 2: left from Frobenius, right from the flow
        subst hx2
        obtain ⟨d1, d2⟩ := hfro 2 ⟨by norm_num, by norm_num⟩
        have hl : HasDerivWithinAt (fun y => (Lg k y, Pg k y))
            (L'g k 2, -((4 * 2 - k * 2 ^ 2 + R k) * Lg k 2)) (Iic 2) 2 := by
          refine ((d1.prodMk d2).hasDerivWithinAt.congr_of_eventuallyEq ?_ ?_).congr_deriv ?_
          · filter_upwards [self_mem_nhdsWithin] with y hy
            simp only [Lg, Pg, if_pos (show y ≤ 2 from hy)]
          · simp only [Lg, Pg, if_pos (le_refl (2 : ℝ))]
          · simp only [Lg, L'g, if_pos (le_refl (2 : ℝ))]
        have hr : HasDerivWithinAt (fun y => (Lg k y, Pg k y))
            (L'g k 2, -((4 * 2 - k * 2 ^ 2 + R k) * Lg k 2)) (Ici 2) 2 := by
          refine (hder2.congr_of_eventuallyEq ?_ ?_).congr_deriv ?_
          · filter_upwards [self_mem_nhdsWithin] with y hy
            rcases (show 2 ≤ y from hy).lt_or_eq with h | h
            · simp only [Lg, Pg, if_neg (not_le.mpr h)]
            · subst h
              simp only [Lg, Pg, if_pos (le_refl (2 : ℝ)), hS2]
              norm_num
          · simp only [Lg, Pg, if_pos (le_refl (2 : ℝ)), hS2]; norm_num
          · simp only [vf, Lg, L'g, if_pos (le_refl (2 : ℝ)), hS2]
            norm_num
        have := hl.union hr
        rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
      · -- flow side
        have hmem : Ioi (2 : ℝ) ∈ 𝓝 x := Ioi_mem_nhds hx2
        refine ((hder x hx2).congr_of_eventuallyEq ?_).congr_deriv ?_
        · filter_upwards [hmem] with y hy
          simp only [Lg, Pg, if_neg (not_le.mpr (show (2 : ℝ) < y from hy))]
        · simp only [vf, Lg, L'g, if_neg (not_le.mpr hx2)]
    have kf := key.hasFDerivAt.fst.hasDerivAt
    have ks := key.hasFDerivAt.snd.hasDerivAt
    refine ⟨?_, ?_⟩
    · simpa using kf
    · have e : (fun y => (y ^ 2 - 1) * L'g k y) = fun y => Pg k y := funext fun y => (hPL y).symm
      rw [e]
      simpa using ks
  · -- continuity in k at fixed x
    by_cases hx : x ≤ 2
    · -- Frobenius side: continuity of the series at a fixed point, along (k, R k)
      set S : Set (ℝ × ℝ) := {p | p.1 ∈ Icc (0 : ℝ) 3 ∧ p.2 ∈ Icc (0 : ℝ) 3}
      have hmap : MapsTo (fun k => (k, R k)) (Icc k₁ k₂) S := fun k hk =>
        ⟨⟨by linarith [hk.1], by linarith [hk.2]⟩, hR3 k hk⟩
      have hpair : ContinuousOn (fun k => (k, R k)) (Icc k₁ k₂) := continuousOn_id.prodMk hR
      have hx' : |x - 1| ≤ 5 / 4 := abs_le.mpr ⟨by linarith, by linarith⟩
      have hS : ∀ p ∈ S, FrobParam.Small ((fun _ : ℝ × ℝ => (1 : ℝ)) p) ((fun p : ℝ × ℝ => 4 - p.1 + p.2) p)
          ((fun p : ℝ × ℝ => 4 - 2 * p.1) p) ((fun p : ℝ × ℝ => -p.1) p) := fun p hp => small_of hp.1 hp.2
      have c0 := FrobParam.sol_continuousOn (W := fun _ : ℝ × ℝ => (1 : ℝ))
        (V0 := fun p : ℝ × ℝ => 4 - p.1 + p.2) (V1 := fun p : ℝ × ℝ => 4 - 2 * p.1) (V2 := fun p : ℝ × ℝ => -p.1)
        (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) hS hx'
      have c1 := FrobParam.dsol_continuousOn (W := fun _ : ℝ × ℝ => (1 : ℝ))
        (V0 := fun p : ℝ × ℝ => 4 - p.1 + p.2) (V1 := fun p : ℝ × ℝ => 4 - 2 * p.1) (V2 := fun p : ℝ × ℝ => -p.1)
        (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) hS hx'
      refine ⟨(c0.comp hpair hmap).congr (fun k _ => ?_), (c1.comp hpair hmap).congr (fun k _ => ?_)⟩
      · simp only [Lg, if_pos hx, Function.comp, RL]
      · simp only [L'g, if_pos hx, Function.comp, RLd]
    · -- flow side: the flow of horizon ⌈x⌉₊ + 3 at x
      push Not at hx
      set n := ⌈x⌉₊
      have hxn : x ∈ Icc (2 : ℝ) ((n : ℝ) + 3) := ⟨hx.le, by linarith [Nat.le_ceil x]⟩
      have hc := (hα n).2.1 x hxn
      refine ⟨(continuous_fst.comp_continuousOn hc).congr (fun k _ => ?_),
        ((continuous_fst.comp_continuousOn (continuous_snd.comp_continuousOn hc)).div_const (x ^ 2 - 1)).congr
          (fun k _ => ?_)⟩
      · simp only [Lg, if_neg (not_le.mpr hx), Function.comp, hsdef, n]
      · simp only [L'g, if_neg (not_le.mpr hx), Function.comp, hsdef, n]

  · -- joint continuity on [k₁, k₂] × [1, B]: Frobenius on [1, 2], the flow of horizon ⌈B⌉₊ + 3 on [2, B]
    set S : Set (ℝ × ℝ) := {p | p.1 ∈ Icc (0 : ℝ) 3 ∧ p.2 ∈ Icc (0 : ℝ) 3}
    have hS : ∀ p ∈ S, FrobParam.Small ((fun _ : ℝ × ℝ => (1 : ℝ)) p) ((fun p : ℝ × ℝ => 4 - p.1 + p.2) p)
        ((fun p : ℝ × ℝ => 4 - 2 * p.1) p) ((fun p : ℝ × ℝ => -p.1) p) := fun p hp => small_of hp.1 hp.2
    have c0 := FrobParam.sol_continuousOn₂ (W := fun _ : ℝ × ℝ => (1 : ℝ))
      (V0 := fun p : ℝ × ℝ => 4 - p.1 + p.2) (V1 := fun p : ℝ × ℝ => 4 - 2 * p.1) (V2 := fun p : ℝ × ℝ => -p.1)
      (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) hS
    have hm1 : ContinuousOn (fun z : ℝ × ℝ => ((z.1, R z.1), z.2 - 1)) (Icc k₁ k₂ ×ˢ Icc 1 2) :=
      ((continuousOn_fst.prodMk (hR.comp continuousOn_fst (fun z hz => hz.1))).prodMk
        (continuousOn_snd.sub continuousOn_const))
    have hmap1 : MapsTo (fun z : ℝ × ℝ => ((z.1, R z.1), z.2 - 1)) (Icc k₁ k₂ ×ˢ Icc 1 2)
        (S ×ˢ Icc (-(5 / 4)) (5 / 4)) := fun z hz =>
      ⟨⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hR3 z.1 hz.1⟩, ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩
    have p1 : ContinuousOn (fun z : ℝ × ℝ => Lg z.1 z.2) (Icc k₁ k₂ ×ˢ Icc 1 2) := by
      refine (c0.comp hm1 hmap1).congr (fun z hz => ?_)
      simp only [Lg, if_pos hz.2.2, Function.comp, RL]
    set n := ⌈B⌉₊
    have hBn : B ≤ (n : ℝ) + 3 := by linarith [Nat.le_ceil B]
    have p2 : ContinuousOn (fun z : ℝ × ℝ => Lg z.1 z.2) (Icc k₁ k₂ ×ˢ Icc 2 B) := by
      have hj := ((hα n).2.2.mono (prod_mono subset_rfl (Icc_subset_Icc_right hBn)))
      refine (continuous_fst.comp_continuousOn hj).congr (fun z hz => ?_)
      have hk := hz.1
      rcases hz.2.1.lt_or_eq with h | h
      · -- consistency of the flows ⌈ξ⌉₊ and n at ξ
        simp only [Lg, if_neg (not_le.mpr h), Function.comp]
        have hk3 : |z.1| ≤ 3 := abs_le.mpr ⟨by linarith [hk.1], by linarith [hk.2]⟩
        have hA3 : |R z.1| ≤ 3 := abs_le.mpr ⟨by linarith [(hR3 z.1 hk).1], (hR3 z.1 hk).2⟩
        have hsn : ∀ m : ℕ, ∀ t ∈ Icc (2 : ℝ) ((m : ℝ) + 3),
            HasDerivWithinAt (s z.1 m) (vf z.1 (R z.1) t (s z.1 m t)) (Icc 2 ((m : ℝ) + 3)) t := by
          intro m t ht
          obtain ⟨h1, h2⟩ := (hα m).1 z.1 hk |>.2 t ht
          exact h1.prodMk h2
        have hs2 : ∀ m, s z.1 m 2 = (RL z.1 (R z.1) 1, 3 * RLd z.1 (R z.1) 1) := by
          intro m
          have e := ((hα m).1 z.1 hk).1
          simp only [hsdef]
          rw [e]
          simp only [p0]
        have cons := (glue_family hk3 hA3 (s z.1) hs2 hsn).1
        have := cons ⌈z.2⌉₊ n z.2 ⟨hz.2.1, by linarith [Nat.le_ceil z.2]⟩ (hz.2.2.trans hBn)
        rw [this]
      · -- at ξ = 2 the flow starts from the Frobenius value
        have e := ((hα n).1 z.1 hk).1
        have hz2 : z.2 = 2 := h.symm
        simp only [Function.comp]
        rw [hz2, e]
        simp only [Lg, if_pos (le_refl (2 : ℝ)), p0]
        norm_num
    have hu : Icc k₁ k₂ ×ˢ Icc (1 : ℝ) B = Icc k₁ k₂ ×ˢ Icc 1 2 ∪ Icc k₁ k₂ ×ˢ Icc 2 B := by
      rw [← prod_union, Icc_union_Icc_eq_Icc (by norm_num) hB]
    rw [hu]
    exact p1.union_of_isClosed p2 (isClosed_Icc.prod isClosed_Icc) (isClosed_Icc.prod isClosed_Icc)

end Work.Quantum.RadialGlobal
