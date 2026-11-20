import Checked.Math.GelfandExists
import Checked.Math.GNegLeft
import Checked.Math.GNegRight

/-! Gelfand problem with a negative parameter: the profile v'' + (2/s) v' = e^{min v M}, v(0) = 0, glued from
the two pieces, and elementary bounds on it (monotonicity only). -/

namespace Checked.Math.GNegProfile
open Set Filter Topology

/-- For 1/8 ≤ M and S ≥ 1/2 there exist w, φ with w differentiable within [0, S] with derivative φ, φ
continuous at 0, φ' = −(2/s)φ + e^{min w M} on (0, S], w(0) = 0 and w ≤ 1/8 on [0, 1/2]. -/
theorem gn_exists_solution (M S : ℝ) (hM : 1 / 8 ≤ M) (hS : 1 / 2 ≤ S) : ∃ w φ : ℝ → ℝ,
    (∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt w (φ s) (Icc 0 S) s) ∧
    ContinuousWithinAt φ (Icc 0 S) 0 ∧
    (∀ s ∈ Ioc (0 : ℝ) S,
      HasDerivWithinAt φ (-(2 / s * φ s) + Real.exp (min (w s) M)) (Icc 0 S) s) ∧
    w 0 = 0 ∧ (∀ s ∈ Icc (0 : ℝ) (1 / 2), w s ≤ 1 / 8) := by
  obtain ⟨wL, φL, h0, hcφ, hwb, hφb, hφb', hdw, hdφ⟩ := Checked.Math.GNegLeft.exists_left
  obtain ⟨wR, φR, hwR, hφR, hR⟩ :=
    Checked.Math.GNegRight.exists_right S M (wL (1 / 2)) (φL (1 / 2)) hS hφb hφb'
  set w : ℝ → ℝ := fun y => if y ≤ 1 / 2 then wL y else wR y with hw
  set φ : ℝ → ℝ := fun y => if y ≤ 1 / 2 then φL y else φR y with hφ
  have wl : ∀ y, y ≤ 1 / 2 → w y = wL y := fun y h => by rw [hw]; exact if_pos h
  have φl : ∀ y, y ≤ 1 / 2 → φ y = φL y := fun y h => by rw [hφ]; exact if_pos h
  have wr : ∀ y, 1 / 2 ≤ y → w y = wR y := fun y h => by
    rcases eq_or_lt_of_le h with h | h
    · subst h; rw [hw]; exact (if_pos le_rfl).trans hwR.symm
    · rw [hw]; exact if_neg (not_le.2 h)
  have φr : ∀ y, 1 / 2 ≤ y → φ y = φR y := fun y h => by
    rcases eq_or_lt_of_le h with h | h
    · subst h; rw [hφ]; exact (if_pos le_rfl).trans hφR.symm
    · rw [hφ]; exact if_neg (not_le.2 h)
  refine ⟨w, φ, fun s hs => ?_, ?_, fun s hs => ?_, (wl 0 (by norm_num)).trans h0,
    fun s hs => by rw [wl s hs.2]; exact hwb s hs⟩
  · exact Checked.Math.GelfandExists.glue hs hS hwR.symm
      (fun h => by rw [φl s h]; exact hdw s ⟨hs.1, h⟩)
      (fun h => by rw [φr s h]; exact (hR s ⟨h, hs.2⟩).1)
  · have e : φ =ᶠ[𝓝[Icc 0 S] 0] φL := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))]
        with y hy using φl y (le_of_lt hy)
    exact (hcφ.continuousWithinAt).congr_of_eventuallyEq e (φl 0 (by norm_num))
  · have hs' : s ∈ Icc (0 : ℝ) S := Ioc_subset_Icc_self hs
    exact Checked.Math.GelfandExists.glue
      (d := fun y => -(2 / y * φ y) + Real.exp (min (w y) M)) hs' hS hφR.symm
      (fun h => by
        have hb := hwb s ⟨hs.1.le, h⟩
        simp only [φl s h, wl s h, min_eq_left (hb.trans hM)]; exact hdφ s ⟨hs.1, h⟩)
      (fun h => by
        simp only [φr s h, wr s h]; exact (hR s ⟨h, hs.2⟩).2)

/-- Lower bounds for the clamped profile: w monotone, w(t) ≥ t²/6. -/
theorem gn_profile_lower (M S : ℝ) (hM : 0 ≤ M) (hS : 0 < S) (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt w (φ s) (Icc 0 S) s)
    (hφ0 : ContinuousWithinAt φ (Icc 0 S) 0)
    (hφ : ∀ s ∈ Ioc (0 : ℝ) S,
      HasDerivWithinAt φ (-(2 / s * φ s) + Real.exp (min (w s) M)) (Icc 0 S) s)
    (h0 : w 0 = 0) :
    MonotoneOn w (Icc 0 S) ∧ ∀ t ∈ Icc (0 : ℝ) S, t ^ 2 / 6 ≤ w t := by
  have h0S : (0 : ℝ) ∈ Icc 0 S := ⟨le_rfl, hS.le⟩
  have cφ : ContinuousOn φ (Icc 0 S) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h]; exact hφ0
    · exact (hφ t ⟨h, ht.2⟩).continuousWithinAt
  have cw : ContinuousOn w (Icc 0 S) := fun t ht => (hw t ht).continuousWithinAt
  have io : ∀ t ∈ interior (Icc (0 : ℝ) S), t ∈ Ioc (0 : ℝ) S ∧ t ∈ Icc (0 : ℝ) S := by
    intro t ht; rw [interior_Icc] at ht; exact ⟨⟨ht.1, ht.2.le⟩, ⟨ht.1.le, ht.2.le⟩⟩
  set q : ℝ → ℝ := fun t => t ^ 2 * φ t with hq
  have dq : ∀ t ∈ Ioc (0 : ℝ) S,
      HasDerivWithinAt q (t ^ 2 * Real.exp (min (w t) M)) (Icc 0 S) t := by
    intro t ht
    have h := ((hasDerivAt_pow 2 t).hasDerivWithinAt (s := Icc 0 S)).mul (hφ t ht)
    convert h using 1
    have : t ≠ 0 := ht.1.ne'
    field_simp
    ring
  have cq : ContinuousOn q (Icc 0 S) := (continuousOn_id.pow 2).mul cφ
  have q0 : q 0 = 0 := by simp [hq]
  have qmono : MonotoneOn q (Icc 0 S) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 S) cq
      (fun t ht => ((dq t (io t ht).1).mono interior_subset))
      (fun t ht => by
        have := Real.exp_pos (min (w t) M)
        positivity)
  have φge0 : ∀ t ∈ Ioc (0 : ℝ) S, 0 ≤ φ t := fun t ht => by
    have h := qmono h0S ⟨ht.1.le, ht.2⟩ ht.1.le
    rw [q0] at h
    have ht2 : 0 < t ^ 2 := by have := ht.1; positivity
    simp only [hq] at h
    by_contra hc; push_neg at hc; nlinarith [mul_pos ht2 (neg_pos.2 hc)]
  have wmono : MonotoneOn w (Icc 0 S) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 S) cw
      (fun t ht => ((hw t (io t ht).2).mono interior_subset))
      (fun t ht => φge0 t (io t ht).1)
  have wge0 : ∀ t ∈ Icc (0 : ℝ) S, 0 ≤ w t := fun t ht => by
    have := wmono h0S ht ht.1; rwa [h0] at this
  have qmono2 : MonotoneOn (fun t => q t - t ^ 3 / 3) (Icc 0 S) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 S)
      (cq.sub ((continuousOn_id.pow 3).div_const 3))
      (fun t ht => (((dq t (io t ht).1).sub
        (((hasDerivAt_pow 3 t).div_const 3).hasDerivWithinAt)).mono interior_subset))
    intro t ht
    have h1 : 1 ≤ Real.exp (min (w t) M) :=
      Real.one_le_exp (le_min (wge0 t (io t ht).2) hM)
    have : t ^ 2 ≤ t ^ 2 * Real.exp (min (w t) M) := by nlinarith [sq_nonneg t]
    simp only [Nat.cast_ofNat]
    nlinarith
  have φge : ∀ t ∈ Ioc (0 : ℝ) S, t / 3 ≤ φ t := fun t ht => by
    have h := qmono2 h0S ⟨ht.1.le, ht.2⟩ ht.1.le
    simp only [q0] at h
    norm_num at h
    have ht2 : 0 < t ^ 2 := by have := ht.1; positivity
    simp only [hq] at h
    by_contra hc; push_neg at hc
    have : t ^ 2 * φ t < t ^ 2 * (t / 3) := mul_lt_mul_of_pos_left hc ht2
    nlinarith
  have wmono2 : MonotoneOn (fun t => w t - t ^ 2 / 6) (Icc 0 S) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 S)
      (cw.sub ((continuousOn_id.pow 2).div_const 6))
      (fun t ht => (((hw t (io t ht).2).sub
        (((hasDerivAt_pow 2 t).div_const 6).hasDerivWithinAt)).mono interior_subset))
    intro t ht
    have := φge t (io t ht).1
    simp only [Nat.cast_ofNat]
    linarith
  refine ⟨wmono, fun t ht => ?_⟩
  have := wmono2 h0S ht ht.1
  simp only [h0] at this
  norm_num at this
  linarith

/-- Bounds near the centre for the unclamped profile φ' = −(2/s)φ + e^w with w ≤ M, writing B = e^M:
0 ≤ φ ≤ B t/3, 0 ≤ w ≤ B t²/6 and |3 t² φ − t³ e^w| ≤ B² t⁵/15. -/
theorem gn_profile_bounds (M S : ℝ) (hS : 0 < S) (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt w (φ s) (Icc 0 S) s)
    (hφ0 : ContinuousWithinAt φ (Icc 0 S) 0)
    (hφ : ∀ s ∈ Ioc (0 : ℝ) S,
      HasDerivWithinAt φ (-(2 / s * φ s) + Real.exp (w s)) (Icc 0 S) s)
    (h0 : w 0 = 0) (hwM : ∀ t ∈ Icc (0 : ℝ) S, w t ≤ M) :
    (∀ t ∈ Icc (0 : ℝ) S, 0 ≤ φ t ∧ φ t ≤ Real.exp M * t / 3) ∧
    (∀ t ∈ Icc (0 : ℝ) S, 0 ≤ w t ∧ w t ≤ Real.exp M * t ^ 2 / 6) ∧
    (∀ t ∈ Icc (0 : ℝ) S,
      |3 * (t ^ 2 * φ t) - t ^ 3 * Real.exp (w t)| ≤ Real.exp M ^ 2 * t ^ 5 / 15) := by
  set B : ℝ := Real.exp M with hB
  have hB0 : 0 < B := Real.exp_pos M
  have h0S : (0 : ℝ) ∈ Icc 0 S := ⟨le_rfl, hS.le⟩
  have cφ : ContinuousOn φ (Icc 0 S) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h]; exact hφ0
    · exact (hφ t ⟨h, ht.2⟩).continuousWithinAt
  have cw : ContinuousOn w (Icc 0 S) := fun t ht => (hw t ht).continuousWithinAt
  have io : ∀ t ∈ interior (Icc (0 : ℝ) S), t ∈ Ioc (0 : ℝ) S ∧ t ∈ Icc (0 : ℝ) S := by
    intro t ht; rw [interior_Icc] at ht; exact ⟨⟨ht.1, ht.2.le⟩, ⟨ht.1.le, ht.2.le⟩⟩
  set q : ℝ → ℝ := fun t => t ^ 2 * φ t with hq
  have dq : ∀ t ∈ Ioc (0 : ℝ) S,
      HasDerivWithinAt q (t ^ 2 * Real.exp (w t)) (Icc 0 S) t := by
    intro t ht
    have h := ((hasDerivAt_pow 2 t).hasDerivWithinAt (s := Icc 0 S)).mul (hφ t ht)
    convert h using 1
    have : t ≠ 0 := ht.1.ne'
    field_simp
    ring
  have cq : ContinuousOn q (Icc 0 S) := (continuousOn_id.pow 2).mul cφ
  have q0 : q 0 = 0 := by simp [hq]
  have ewle : ∀ t ∈ Icc (0 : ℝ) S, Real.exp (w t) ≤ B := fun t ht =>
    Real.exp_le_exp.2 (hwM t ht)
  have qmono : MonotoneOn q (Icc 0 S) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 S) cq
      (fun t ht => ((dq t (io t ht).1).mono interior_subset))
      (fun t ht => by
        have := Real.exp_pos (w t)
        positivity)
  have φge0' : ∀ t ∈ Ioc (0 : ℝ) S, 0 ≤ φ t := fun t ht => by
    have h := qmono h0S ⟨ht.1.le, ht.2⟩ ht.1.le
    rw [q0] at h
    have ht2 : 0 < t ^ 2 := by have := ht.1; positivity
    simp only [hq] at h
    by_contra hc; push_neg at hc; nlinarith [mul_pos ht2 (neg_pos.2 hc)]
  have hne : (𝓝[Ioc (0 : ℝ) S] (0 : ℝ)).NeBot := left_nhdsWithin_Ioc_neBot hS
  have tφ : Tendsto φ (𝓝[Ioc (0 : ℝ) S] 0) (𝓝 (φ 0)) :=
    (hφ0.mono Ioc_subset_Icc_self).tendsto
  have φge0 : ∀ t ∈ Icc (0 : ℝ) S, 0 ≤ φ t := fun t ht => by
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h]
      exact ge_of_tendsto tφ (eventually_nhdsWithin_of_forall fun t ht => φge0' t ht)
    · exact φge0' t ⟨h, ht.2⟩
  have wmono : MonotoneOn w (Icc 0 S) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 S) cw
      (fun t ht => ((hw t (io t ht).2).mono interior_subset))
      (fun t ht => φge0 t (io t ht).2)
  have wge0 : ∀ t ∈ Icc (0 : ℝ) S, 0 ≤ w t := fun t ht => by
    have := wmono h0S ht ht.1; rwa [h0] at this
  -- q ≤ B t³/3
  have qanti : AntitoneOn (fun t => q t - B * t ^ 3 / 3) (Icc 0 S) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 S)
      (cq.sub (((continuousOn_id.pow 3).const_smul B).div_const 3))
      (fun t ht => (((dq t (io t ht).1).sub
        ((((hasDerivAt_pow 3 t).const_mul B).div_const 3).hasDerivWithinAt)).mono interior_subset))
    intro t ht
    have := ewle t (io t ht).2
    have : t ^ 2 * Real.exp (w t) ≤ t ^ 2 * B := mul_le_mul_of_nonneg_left this (sq_nonneg t)
    simp only [Nat.cast_ofNat]
    nlinarith
  have φle' : ∀ t ∈ Ioc (0 : ℝ) S, φ t ≤ B * t / 3 := fun t ht => by
    have h := qanti h0S ⟨ht.1.le, ht.2⟩ ht.1.le
    simp only [q0] at h
    norm_num at h
    have ht2 : 0 < t ^ 2 := by have := ht.1; positivity
    simp only [hq] at h
    by_contra hc; push_neg at hc
    have : t ^ 2 * (B * t / 3) < t ^ 2 * φ t := mul_lt_mul_of_pos_left hc ht2
    nlinarith
  have φle : ∀ t ∈ Icc (0 : ℝ) S, φ t ≤ B * t / 3 := fun t ht => by
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h]
      have hl : Tendsto (fun t => B * t / 3) (𝓝[Ioc (0 : ℝ) S] 0) (𝓝 (B * 0 / 3)) :=
        (((continuous_const.mul continuous_id).div_const 3).tendsto 0).mono_left nhdsWithin_le_nhds
      exact le_of_tendsto_of_tendsto tφ hl
        (eventually_nhdsWithin_of_forall fun t ht => φle' t ht)
    · exact φle' t ⟨h, ht.2⟩
  -- w ≤ B t²/6
  have wanti : AntitoneOn (fun t => w t - B * t ^ 2 / 6) (Icc 0 S) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 S)
      (cw.sub (((continuousOn_id.pow 2).const_smul B).div_const 6))
      (fun t ht => (((hw t (io t ht).2).sub
        ((((hasDerivAt_pow 2 t).const_mul B).div_const 6).hasDerivWithinAt)).mono interior_subset))
    intro t ht
    have := φle t (io t ht).2
    simp only [Nat.cast_ofNat]
    nlinarith
  have wle : ∀ t ∈ Icc (0 : ℝ) S, w t ≤ B * t ^ 2 / 6 := fun t ht => by
    have := wanti h0S ht ht.1
    simp only [h0] at this
    norm_num at this
    linarith
  -- D = 3q − t³ eʷ
  set D : ℝ → ℝ := fun t => 3 * q t - t ^ 3 * Real.exp (w t) with hD
  have dD : ∀ t ∈ Ioc (0 : ℝ) S,
      HasDerivWithinAt D (-(t ^ 3 * Real.exp (w t) * φ t)) (Icc 0 S) t := by
    intro t ht
    have h := ((dq t ht).const_mul 3).sub
      (((hasDerivAt_pow 3 t).hasDerivWithinAt (s := Icc 0 S)).mul
        ((hw t ⟨ht.1.le, ht.2⟩).exp))
    convert h using 1
    simp only [Nat.cast_ofNat]
    ring
  have cD : ContinuousOn D (Icc 0 S) :=
    (cq.const_smul (3 : ℝ)).sub ((continuousOn_id.pow 3).mul (cw.rexp))
  have D0 : D 0 = 0 := by simp [hD, q0]
  have dbound : ∀ t ∈ Icc (0 : ℝ) S, |-(t ^ 3 * Real.exp (w t) * φ t)| ≤ B ^ 2 * t ^ 4 / 3 := by
    intro t ht
    have h1 := φge0 t ht; have h2 := φle t ht; have h3 := ewle t ht
    have h4 := Real.exp_pos (w t)
    have ht3 : 0 ≤ t ^ 3 := by have := ht.1; positivity
    rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg ht3, abs_of_pos h4, abs_of_nonneg h1]
    have h5 : t ^ 3 * Real.exp (w t) ≤ t ^ 3 * B := mul_le_mul_of_nonneg_left h3 ht3
    calc t ^ 3 * Real.exp (w t) * φ t ≤ t ^ 3 * B * (B * t / 3) :=
          mul_le_mul h5 h2 h1 (by positivity)
      _ = B ^ 2 * t ^ 4 / 3 := by ring
  have Dup : MonotoneOn (fun t => B ^ 2 * t ^ 5 / 15 - D t) (Icc 0 S) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 S)
      ((((continuousOn_id.pow 5).const_smul (B ^ 2)).div_const 15).sub cD)
      (fun t ht => (((((hasDerivAt_pow 5 t).const_mul (B ^ 2)).div_const 15).hasDerivWithinAt.sub
        (dD t (io t ht).1)).mono interior_subset))
    intro t ht
    have := (abs_le.1 (dbound t (io t ht).2)).2
    simp only [Nat.cast_ofNat]
    have e : B ^ 2 * ((5 : ℝ) * t ^ 4) / 15 = B ^ 2 * t ^ 4 / 3 := by ring
    linarith
  have Dlo : MonotoneOn (fun t => B ^ 2 * t ^ 5 / 15 + D t) (Icc 0 S) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 S)
      ((((continuousOn_id.pow 5).const_smul (B ^ 2)).div_const 15).add cD)
      (fun t ht => (((((hasDerivAt_pow 5 t).const_mul (B ^ 2)).div_const 15).hasDerivWithinAt.add
        (dD t (io t ht).1)).mono interior_subset))
    intro t ht
    have := (abs_le.1 (dbound t (io t ht).2)).1
    simp only [Nat.cast_ofNat]
    have e : B ^ 2 * ((5 : ℝ) * t ^ 4) / 15 = B ^ 2 * t ^ 4 / 3 := by ring
    linarith
  refine ⟨fun t ht => ⟨φge0 t ht, φle t ht⟩, fun t ht => ⟨wge0 t ht, wle t ht⟩, fun t ht => ?_⟩
  have a := Dup h0S ht ht.1
  have b := Dlo h0S ht ht.1
  simp only [D0] at a b
  norm_num at a b
  rw [abs_le]
  exact ⟨by simp only [hD] at b; linarith, by simp only [hD] at a; linarith⟩

end Checked.Math.GNegProfile
