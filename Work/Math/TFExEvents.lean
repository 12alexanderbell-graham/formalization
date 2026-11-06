import Mathlib
import Work.Math.TFExBase

/-!
# Thomas–Fermi existence: the two shooting events of the clamped system

For a solution (u, Φ) of the clamped system u' = 2t·cl(Φ), Φ' = 2g(min u 2) on [0, T]
(`Work.Math.TFExBase`): Φ is nondecreasing; once u is negative somewhere, Φ ≤ 0 on the whole
interval (so "u goes negative" and "Φ goes positive" exclude each other); the slope −10 makes
u negative at t = 1/2; the slope 0 makes Φ positive.
-/

namespace Work.Math.TFExEvents
open Set Filter Topology Work.Math.TFExBase

theorem toIci {T x f' : ℝ} {f : ℝ → ℝ} (hx : x ∈ Ico 0 T)
    (h : HasDerivWithinAt f f' (Icc 0 T) x) : HasDerivWithinAt f f' (Ici x) x :=
  h.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hx)

theorem g_le_three {v : ℝ} (hv : v ≤ 2) : g v ≤ 3 := by
  unfold g
  have h1 : max v 0 ≤ 2 := max_le hv (by norm_num)
  have h2 : Real.sqrt (max v 0) ≤ 3 / 2 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
  have h3 : 0 ≤ max v 0 := le_max_right _ _
  have h4 : 0 ≤ Real.sqrt (max v 0) := Real.sqrt_nonneg _
  nlinarith

section
variable {T : ℝ} {u Φ : ℝ → ℝ}
  (hu : ∀ t ∈ Icc 0 T, HasDerivWithinAt u (2 * t * cl 10 (Φ t)) (Icc 0 T) t)
  (hΦ : ∀ t ∈ Icc 0 T, HasDerivWithinAt Φ (2 * g (min (u t) 2)) (Icc 0 T) t)
include hu hΦ

omit hu in
theorem phi_mono : MonotoneOn Φ (Icc 0 T) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 T)
    (fun t ht => (hΦ t ht).continuousWithinAt)
    (fun x hx => (hΦ x (interior_subset hx)).mono interior_subset) (fun x _ => ?_)
  have := g_nonneg (min (u x) 2); linarith

omit hu in
theorem const_phi {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T)
    (hneg : ∀ x ∈ Ico a b, u x ≤ 0) : ∀ x ∈ Icc a b, Φ x = Φ a := by
  refine constant_of_has_deriv_right_zero
    (fun t ht => ((hΦ t ⟨ha.trans ht.1, ht.2.trans hb⟩).continuousWithinAt).mono
      (Icc_subset_Icc ha hb)) (fun x hx => ?_)
  have h := toIci ⟨ha.trans hx.1, hx.2.trans_le hb⟩ (hΦ x ⟨ha.trans hx.1, hx.2.le.trans hb⟩)
  rwa [g_of_nonpos (min_le_of_left_le (hneg x hx)), mul_zero] at h

omit hΦ in
theorem u_le {a b c : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T)
    (hc : ∀ x ∈ Icc a b, Φ x = c) (hc0 : c ≤ 0) : u b ≤ u a := by
  have hcl : cl 10 c ≤ 0 := not_lt.mp (fun h => absurd (cl_pos_iff.mp h) (not_lt.mpr hc0))
  have := image_le_of_deriv_right_le_deriv_boundary (f := u) (a := a) (b := b)
    (f' := fun x => 2 * x * cl 10 (Φ x)) (B := fun _ => u a) (B' := fun _ => 0)
    (fun t ht => ((hu t ⟨ha.trans ht.1, ht.2.trans hb⟩).continuousWithinAt).mono
      (Icc_subset_Icc ha hb))
    (fun x hx => toIci ⟨ha.trans hx.1, hx.2.trans_le hb⟩
      (hu x ⟨ha.trans hx.1, hx.2.le.trans hb⟩)) le_rfl continuousOn_const
    (fun x _ => hasDerivWithinAt_const _ _ _)
    (fun x hx => by
      rw [hc x (Ico_subset_Icc_self hx)]
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith [hx.1]) hcl) ⟨hab, le_rfl⟩
  exact this

omit hΦ in
theorem u_ge {a b c : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T)
    (hc : ∀ x ∈ Icc a b, Φ x = c) (hc0 : 0 ≤ c) : u a ≤ u b := by
  have hcl : 0 ≤ cl 10 c := by
    rcases hc0.lt_or_eq with h | h
    · exact (cl_pos_iff.mpr h).le
    · rw [← h]; simp [cl]
  have := image_le_of_deriv_right_le_deriv_boundary (f := fun _ => u a) (a := a) (b := b)
    (f' := fun _ => 0) (B := u) (B' := fun x => 2 * x * cl 10 (Φ x)) continuousOn_const
    (fun x _ => hasDerivWithinAt_const _ _ _) le_rfl
    (fun t ht => ((hu t ⟨ha.trans ht.1, ht.2.trans hb⟩).continuousWithinAt).mono
      (Icc_subset_Icc ha hb))
    (fun x hx => toIci ⟨ha.trans hx.1, hx.2.trans_le hb⟩
      (hu x ⟨ha.trans hx.1, hx.2.le.trans hb⟩))
    (fun x hx => by
      rw [hc x (Ico_subset_Icc_self hx)]
      exact mul_nonneg (by linarith [hx.1]) hcl) ⟨hab, le_rfl⟩
  exact this

/-- once u is negative somewhere, Φ ≤ 0 everywhere on [0, T] (so the two shooting events
exclude each other) -/
theorem excl (hu0 : u 0 = 1) (ha : ∃ t ∈ Icc 0 T, u t < 0) : ∀ t ∈ Icc 0 T, Φ t ≤ 0 := by
  obtain ⟨ta, hta, huta⟩ := ha
  have cu : ContinuousOn u (Icc 0 T) := fun t ht => (hu t ht).continuousWithinAt
  -- m: last time in [0, ta] with u ≥ 0
  set S : Set ℝ := Icc 0 ta ∩ u ⁻¹' Ici 0 with hSdef
  have hSc : IsClosed S :=
    (cu.mono (Icc_subset_Icc_right hta.2)).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have h0S : (0 : ℝ) ∈ S := ⟨⟨le_rfl, hta.1⟩, by simp [hu0]⟩
  have hbdd : BddAbove S := ⟨ta, fun x hx => hx.1.2⟩
  set m := sSup S with hm
  have hmS : m ∈ S := hSc.csSup_mem ⟨0, h0S⟩ hbdd
  have hm0 : 0 ≤ m := hmS.1.1
  have hmta : m ≤ ta := hmS.1.2
  have hum : 0 ≤ u m := hmS.2
  have hmlt : m < ta := lt_of_le_of_ne hmta (fun h => by rw [h] at hum; linarith)
  have hneg1 : ∀ t ∈ Ioc m ta, u t < 0 := by
    intro t ht
    by_contra h
    have : t ∈ S := ⟨⟨hm0.trans ht.1.le, ht.2⟩, le_of_not_gt h⟩
    exact absurd (le_csSup hbdd this) (not_le.mpr ht.1)
  have hum' : u m ≤ 0 := by
    have hcw : ContinuousWithinAt u (Ioc m ta) m :=
      (cu m ⟨hm0, hmta.trans hta.2⟩).mono (fun t ht => ⟨hm0.trans ht.1.le, ht.2.trans hta.2⟩)
    have hcl : m ∈ closure (Ioc m ta) := by
      rw [closure_Ioc hmlt.ne]; exact ⟨le_rfl, hmta⟩
    have := hcw.mem_closure hcl (show MapsTo u (Ioc m ta) (Iic 0) from fun t ht => (hneg1 t ht).le)
    rwa [isClosed_Iic.closure_eq] at this
  have hT : ta ≤ T := hta.2
  -- Φ constant on [m, ta], and negative there
  have hconst1 := const_phi hΦ hm0 hmta hT (fun x hx => by
    rcases eq_or_lt_of_le hx.1 with h | h
    · rw [← h]; exact hum'
    · exact (hneg1 x ⟨h, hx.2.le⟩).le)
  have hΦm : Φ m < 0 := by
    by_contra h
    have := u_ge hu hm0 hmta hT hconst1 (le_of_not_gt h)
    linarith
  -- u stays negative on [ta, T]
  have hneg2 : ∀ t ∈ Icc ta T, u t < 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨t1, ht1, hut1⟩ := hcon
    set B : Set ℝ := Icc ta T ∩ u ⁻¹' Ici 0 with hBdef
    have hBc : IsClosed B :=
      (cu.mono (Icc_subset_Icc_left hta.1)).preimage_isClosed_of_isClosed isClosed_Icc
        isClosed_Ici
    have hBne : B.Nonempty := ⟨t1, ht1, hut1⟩
    have hBb : BddBelow B := ⟨ta, fun x hx => hx.1.1⟩
    set q := sInf B with hq
    have hqB : q ∈ B := hBc.csInf_mem hBne hBb
    have hqta : ta < q := lt_of_le_of_ne hqB.1.1 (fun h => by
      have := hqB.2; rw [← h] at this; simp at this; linarith)
    have hqT : q ≤ T := hqB.1.2
    have hlt : ∀ x ∈ Ico ta q, u x < 0 := by
      intro x hx
      by_contra h
      have : x ∈ B := ⟨⟨hx.1, hx.2.le.trans hqT⟩, le_of_not_gt h⟩
      exact absurd (csInf_le hBb this) (not_le.mpr hx.2)
    have hconst2 := const_phi hΦ hm0 (hmta.trans hqta.le) hqT (fun x hx => by
      rcases eq_or_lt_of_le hx.1 with h | h
      · rw [← h]; exact hum'
      · rcases le_or_gt x ta with h' | h'
        · exact (hneg1 x ⟨h, h'⟩).le
        · exact (hlt x ⟨h'.le, hx.2⟩).le)
    have := u_le hu (hm0.trans hmta) hqta.le hqT
      (fun x hx => hconst2 x ⟨hmta.trans hx.1, hx.2⟩) hΦm.le
    have := hqB.2
    simp only [mem_preimage, mem_Ici] at this
    linarith
  have hconst3 := const_phi hΦ hm0 (hmta.trans hT) le_rfl (fun x hx => by
    rcases eq_or_lt_of_le hx.1 with h | h
    · rw [← h]; exact hum'
    · rcases le_or_gt x ta with h' | h'
      · exact (hneg1 x ⟨h, h'⟩).le
      · exact (hneg2 x ⟨h'.le, hx.2.le⟩).le)
  intro t ht
  rcases le_or_gt t m with h | h
  · have := phi_mono hΦ ht ⟨hm0, hmta.trans hT⟩ h
    linarith
  · rw [hconst3 t ⟨h.le, ht.2⟩]; exact hΦm.le

/-- slope −10: u is negative at t = 1/2 -/
theorem low_event (hT : 1 / 2 ≤ T) (hu0 : u 0 = 1) (hs : Φ 0 = -10) : u (1 / 2) < 0 := by
  have hsub : ∀ x ∈ Icc (0 : ℝ) (1 / 2), x ∈ Icc 0 T := fun x hx => ⟨hx.1, hx.2.trans hT⟩
  have hsub' : ∀ x ∈ Ico (0 : ℝ) (1 / 2), x ∈ Ico 0 T :=
    fun x hx => ⟨hx.1, hx.2.trans_le hT⟩
  -- Φ ≤ −10 + 6t
  have hup : ∀ x ∈ Icc (0 : ℝ) (1 / 2), Φ x ≤ -10 + 6 * x := by
    refine image_le_of_deriv_right_le_deriv_boundary (f := Φ)
      (f' := fun x => 2 * g (min (u x) 2)) (B := fun x => -10 + 6 * x) (B' := fun _ => 6)
      (fun t ht => ((hΦ t (hsub t ht)).continuousWithinAt).mono (fun x hx => hsub x hx))
      (fun x hx => toIci (hsub' x hx) (hΦ x (hsub x (Ico_subset_Icc_self hx))))
      (by rw [hs]; norm_num) (by fun_prop) (fun x _ => ?_) (fun x _ => ?_)
    · have := ((hasDerivAt_id x).const_mul 6).const_add (-10)
      simpa using this.hasDerivWithinAt
    · have := g_le_three (min_le_right (u x) 2); linarith
  have hlo : ∀ x ∈ Icc (0 : ℝ) (1 / 2), -10 ≤ Φ x := fun x hx => by
    have := phi_mono hΦ ⟨le_rfl, (by linarith : (0:ℝ) ≤ T)⟩ (hsub x hx) hx.1
    rwa [hs] at this
  have hcl : ∀ x ∈ Icc (0 : ℝ) (1 / 2), cl 10 (Φ x) = Φ x := fun x hx => by
    apply cl_of_abs_le; rw [abs_le]
    exact ⟨hlo x hx, by linarith [hup x hx, hx.2]⟩
  have key : ∀ x ∈ Icc (0 : ℝ) (1 / 2), u x ≤ 1 - 10 * x ^ 2 + 4 * x ^ 3 := by
    refine image_le_of_deriv_right_le_deriv_boundary (f := u)
      (f' := fun x => 2 * x * cl 10 (Φ x)) (B := fun x => 1 - 10 * x ^ 2 + 4 * x ^ 3)
      (B' := fun x => -20 * x + 12 * x ^ 2)
      (fun t ht => ((hu t (hsub t ht)).continuousWithinAt).mono (fun x hx => hsub x hx))
      (fun x hx => toIci (hsub' x hx) (hu x (hsub x (Ico_subset_Icc_self hx))))
      (by rw [hu0]; norm_num) (by fun_prop) (fun x _ => ?_) (fun x hx => ?_)
    · have := ((((hasDerivAt_id x).pow 2).const_mul 10).const_sub 1).add
        (((hasDerivAt_id x).pow 3).const_mul 4)
      convert this.hasDerivWithinAt using 1
      · ext y; simp
      · simp; ring
    · have hx' := Ico_subset_Icc_self hx
      rw [hcl x hx']
      have := hup x hx'
      nlinarith [hx.1]
  have := key (1 / 2) ⟨by norm_num, le_rfl⟩
  linarith

/-- slope 0: Φ becomes positive -/
theorem high_event (hT : 0 < T) (hu0 : u 0 = 1) (hs : Φ 0 = 0) : ∃ t ∈ Icc 0 T, 0 < Φ t := by
  by_contra hcon
  push Not at hcon
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hz : ∀ t ∈ Icc 0 T, Φ t = 0 := fun t ht => by
    have := phi_mono hΦ h0 ht ht.1
    rw [hs] at this
    linarith [hcon t ht]
  have hd0 : HasDerivWithinAt Φ 0 (Icc 0 T) 0 :=
    (hasDerivWithinAt_const (0 : ℝ) (Icc 0 T) (0 : ℝ)).congr (fun t ht => hz t ht) (hz 0 h0)
  have heq := (uniqueDiffOn_Icc hT 0 h0).eq_deriv _ (hΦ 0 h0) hd0
  rw [hu0, min_eq_left (by norm_num : (1 : ℝ) ≤ 2)] at heq
  have := g_pos (by norm_num : (0 : ℝ) < 1)
  linarith

end

end Work.Math.TFExEvents
