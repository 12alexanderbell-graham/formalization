import Mathlib

/-!
# Thomas–Fermi equation: reduction to the cooperative system in t = √x, w = √y

For a solution y of the Thomas–Fermi problem (hypotheses of
`Work.Math.ThomasFermi.tf_initial_slope`): the slope φ is negative on [0, ∞) (`phi_neg`);
W t = √(y(t²)) and P t = φ(t²) are continuous, W > 0, W 0 = 1, and for t > 0
W' = t·P/W, P' = 2W³ (`deriv_W`, `deriv_P`); and if at some t₁ > 0 the state is small and
steep enough (4ω⁵ < t₁π², W(t₁) ≤ ω, P(t₁) ≤ −π) the solution would reach zero (`zero_event`).
-/

namespace Work.Math.TFReduce
open Set Filter Topology

theorem phi_contOn (y φ : ℝ → ℝ)
    (hφ : ∀ x, 0 < x → HasDerivAt φ (y x ^ ((3 : ℝ) / 2) / Real.sqrt x) x)
    (hφ0 : ContinuousWithinAt φ (Ici 0) 0) : ContinuousOn φ (Ici 0) := by
  intro x hx
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ x from hx) with h | h
  · rw [← h]; exact hφ0
  · exact (hφ x h).continuousAt.continuousWithinAt

theorem phi_strictMono (y φ : ℝ → ℝ)
    (hφ : ∀ x, 0 < x → HasDerivAt φ (y x ^ ((3 : ℝ) / 2) / Real.sqrt x) x)
    (hφ0 : ContinuousWithinAt φ (Ici 0) 0) (hpos : ∀ x, 0 ≤ x → 0 < y x) :
    StrictMonoOn φ (Ici 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 0) (phi_contOn y φ hφ hφ0) fun x hx => ?_
  rw [interior_Ici] at hx
  have hx' : (0 : ℝ) < x := hx
  rw [(hφ x hx').deriv]
  exact div_pos (Real.rpow_pos_of_pos (hpos x hx'.le) _) (Real.sqrt_pos.2 hx')

theorem y_hasDerivAt (y φ : ℝ → ℝ) (hy : ∀ x, 0 ≤ x → HasDerivWithinAt y (φ x) (Ici 0) x)
    {x : ℝ} (hx : 0 < x) : HasDerivAt y (φ x) x :=
  (hy x hx.le).hasDerivAt (Ici_mem_nhds hx)

theorem y_contOn (y φ : ℝ → ℝ) (hy : ∀ x, 0 ≤ x → HasDerivWithinAt y (φ x) (Ici 0) x) :
    ContinuousOn y (Ici 0) := fun x hx => (hy x hx).continuousWithinAt

/-- The slope is negative everywhere on [0, ∞). -/
theorem phi_neg (y φ : ℝ → ℝ)
    (hy : ∀ x, 0 ≤ x → HasDerivWithinAt y (φ x) (Ici 0) x)
    (hφ : ∀ x, 0 < x → HasDerivAt φ (y x ^ ((3 : ℝ) / 2) / Real.sqrt x) x)
    (hφ0 : ContinuousWithinAt φ (Ici 0) 0) (hpos : ∀ x, 0 ≤ x → 0 < y x)
    (hlim : Tendsto y atTop (𝓝 0)) : ∀ x, 0 ≤ x → φ x < 0 := by
  intro x₀ hx₀
  by_contra hc
  push Not at hc
  have hmono := phi_strictMono y φ hφ hφ0 hpos
  have hφge : ∀ x, x₀ ≤ x → 0 ≤ φ x := fun x hx =>
    hc.trans (hmono.monotoneOn hx₀ (hx₀.trans hx) hx)
  have hymono : MonotoneOn y (Ici x₀) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici x₀)
      ((y_contOn y φ hy).mono (Ici_subset_Ici.2 hx₀)) ?_ ?_
    · intro x hx
      rw [interior_Ici] at hx
      exact (y_hasDerivAt y φ hy (lt_of_le_of_lt hx₀ hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(y_hasDerivAt y φ hy (lt_of_le_of_lt hx₀ hx)).deriv]
      exact hφge x (le_of_lt hx)
  have hge : ∀ᶠ x in atTop, y x₀ ≤ y x :=
    (eventually_ge_atTop x₀).mono fun x hx => hymono (Set.mem_Ici.2 le_rfl) hx hx
  have := ge_of_tendsto hlim hge
  linarith [hpos x₀ hx₀]

theorem cont_Y (y φ : ℝ → ℝ) (hy : ∀ x, 0 ≤ x → HasDerivWithinAt y (φ x) (Ici 0) x) :
    Continuous (fun t : ℝ => y (t ^ 2)) := by
  exact (y_contOn y φ hy).comp_continuous (continuous_pow 2) fun s => sq_nonneg s

theorem cont_W (y φ : ℝ → ℝ) (hy : ∀ x, 0 ≤ x → HasDerivWithinAt y (φ x) (Ici 0) x)
    (T : ℝ) : ContinuousOn (fun t => Real.sqrt (y (t ^ 2))) (Icc 0 T) :=
  (Real.continuous_sqrt.comp (cont_Y y φ hy)).continuousOn

theorem cont_P_glob (y φ : ℝ → ℝ)
    (hφ : ∀ x, 0 < x → HasDerivAt φ (y x ^ ((3 : ℝ) / 2) / Real.sqrt x) x)
    (hφ0 : ContinuousWithinAt φ (Ici 0) 0) : Continuous (fun t : ℝ => φ (t ^ 2)) := by
  exact (phi_contOn y φ hφ hφ0).comp_continuous (continuous_pow 2) fun s => sq_nonneg s

theorem cont_P (y φ : ℝ → ℝ)
    (hφ : ∀ x, 0 < x → HasDerivAt φ (y x ^ ((3 : ℝ) / 2) / Real.sqrt x) x)
    (hφ0 : ContinuousWithinAt φ (Ici 0) 0) (T : ℝ) :
    ContinuousOn (fun t => φ (t ^ 2)) (Icc 0 T) :=
  (cont_P_glob y φ hφ hφ0).continuousOn

theorem W_pos (y : ℝ → ℝ) (hpos : ∀ x, 0 ≤ x → 0 < y x) (t : ℝ) :
    0 < Real.sqrt (y (t ^ 2)) := Real.sqrt_pos.2 (hpos _ (sq_nonneg t))

theorem W_zero (y : ℝ → ℝ) (h0 : y 0 = 1) : Real.sqrt (y (0 ^ 2)) = 1 := by
  simp [h0]

theorem P_zero (φ : ℝ → ℝ) : φ ((0 : ℝ) ^ 2) = φ 0 := by simp

theorem hasDerivAt_sq' (t : ℝ) : HasDerivAt (fun x : ℝ => x ^ 2) (2 * t) t := by
  simpa using hasDerivAt_pow 2 t

theorem deriv_Y (y φ : ℝ → ℝ) (hy : ∀ x, 0 ≤ x → HasDerivWithinAt y (φ x) (Ici 0) x)
    {t : ℝ} (ht : 0 < t) : HasDerivAt (fun t => y (t ^ 2)) (2 * t * φ (t ^ 2)) t := by
  have hy' : HasDerivAt y (φ (t ^ 2)) ((fun x : ℝ => x ^ 2) t) :=
    y_hasDerivAt y φ hy (pow_pos ht 2)
  have h : HasDerivAt (fun t => y (t ^ 2)) (φ (t ^ 2) * (2 * t)) t :=
    HasDerivAt.comp (h := fun x : ℝ => x ^ 2) t hy' (hasDerivAt_sq' t)
  convert h using 1
  ring

theorem deriv_W (y φ : ℝ → ℝ) (hy : ∀ x, 0 ≤ x → HasDerivWithinAt y (φ x) (Ici 0) x)
    (hpos : ∀ x, 0 ≤ x → 0 < y x) :
    ∀ t, 0 < t → HasDerivAt (fun t => Real.sqrt (y (t ^ 2)))
      (t * φ (t ^ 2) / Real.sqrt (y (t ^ 2))) t := by
  intro t ht
  have hY := hpos (t ^ 2) (sq_nonneg t)
  have h := (deriv_Y y φ hy ht).sqrt hY.ne'
  convert h using 1
  have hs : 0 < Real.sqrt (y (t ^ 2)) := Real.sqrt_pos.2 hY
  field_simp

theorem rpow_three_halves {u : ℝ} (hu : 0 < u) : u ^ ((3 : ℝ) / 2) = Real.sqrt u ^ 3 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hu.le]
  norm_num

theorem deriv_P (y φ : ℝ → ℝ)
    (hφ : ∀ x, 0 < x → HasDerivAt φ (y x ^ ((3 : ℝ) / 2) / Real.sqrt x) x)
    (hpos : ∀ x, 0 ≤ x → 0 < y x) :
    ∀ t, 0 < t → HasDerivAt (fun t => φ (t ^ 2)) (2 * Real.sqrt (y (t ^ 2)) ^ 3) t := by
  intro t ht
  have hφ' : HasDerivAt φ (y (t ^ 2) ^ ((3 : ℝ) / 2) / Real.sqrt (t ^ 2))
      ((fun x : ℝ => x ^ 2) t) := hφ (t ^ 2) (pow_pos ht 2)
  have h : HasDerivAt (fun t => φ (t ^ 2))
      (y (t ^ 2) ^ ((3 : ℝ) / 2) / Real.sqrt (t ^ 2) * (2 * t)) t :=
    HasDerivAt.comp (h := fun x : ℝ => x ^ 2) t hφ' (hasDerivAt_sq' t)
  convert h using 1
  rw [rpow_three_halves (hpos _ (sq_nonneg t)), Real.sqrt_sq ht.le]
  field_simp

/-- If at t₁ > 0 the state is small and steep enough, the solution would reach zero. -/
theorem zero_event (y φ : ℝ → ℝ)
    (hy : ∀ x, 0 ≤ x → HasDerivWithinAt y (φ x) (Ici 0) x)
    (hφ : ∀ x, 0 < x → HasDerivAt φ (y x ^ ((3 : ℝ) / 2) / Real.sqrt x) x)
    (hφ0 : ContinuousWithinAt φ (Ici 0) 0) (hpos : ∀ x, 0 ≤ x → 0 < y x)
    (hlim : Tendsto y atTop (𝓝 0)) :
    ∀ t1 ω π : ℝ, 0 < t1 → 0 < ω → 0 < π → 4 * ω ^ 5 < t1 * π ^ 2 →
      Real.sqrt (y (t1 ^ 2)) ≤ ω → φ (t1 ^ 2) ≤ -π → False := by
  intro t1 ω π ht1 hω hπ hcond hW1 hP1
  set W : ℝ → ℝ := fun t => Real.sqrt (y (t ^ 2)) with hWdef
  set P : ℝ → ℝ := fun t => φ (t ^ 2) with hPdef
  have hPneg : ∀ t, P t < 0 := fun t => phi_neg y φ hy hφ hφ0 hpos hlim _ (sq_nonneg t)
  -- W is antitone on [t₁, ∞)
  have hWanti : AntitoneOn W (Ici t1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici t1) (fun t _ =>
      (Real.continuous_sqrt.comp (cont_Y y φ hy)).continuousAt.continuousWithinAt) ?_ ?_
    · intro t ht
      rw [interior_Ici] at ht
      exact (deriv_W y φ hy hpos t (ht1.trans ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have htp : 0 < t := ht1.trans ht
      rw [(deriv_W y φ hy hpos t htp).deriv]
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos htp.le (hPneg t).le) (Real.sqrt_nonneg _)
  have hWle : ∀ t, t1 ≤ t → W t ≤ ω := fun t ht => (hWanti (Set.mem_Ici.2 le_rfl) ht ht).trans hW1
  -- P t − 2ω³ t is antitone on [t₁, ∞)
  have hPanti : AntitoneOn (fun t => P t - 2 * ω ^ 3 * t) (Ici t1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici t1)
      ((cont_P_glob y φ hφ hφ0).sub (continuous_const.mul continuous_id)).continuousOn ?_ ?_
    · intro t ht
      rw [interior_Ici] at ht
      exact ((deriv_P y φ hφ hpos t (ht1.trans ht)).sub
        ((hasDerivAt_id' t).const_mul (2 * ω ^ 3))).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have htp : 0 < t := ht1.trans ht
      have hd : HasDerivAt (fun t => P t - 2 * ω ^ 3 * t) (2 * W t ^ 3 - 2 * ω ^ 3 * 1) t :=
        (deriv_P y φ hφ hpos t htp).sub ((hasDerivAt_id' t).const_mul (2 * ω ^ 3))
      rw [hd.deriv]
      have hw0 : 0 ≤ W t := Real.sqrt_nonneg _
      have := pow_le_pow_left₀ hw0 (hWle t ht.le) 3
      simp only [hWdef] at this
      linarith
  have hω3 : 0 < ω ^ 3 := pow_pos hω 3
  set L := π / (4 * ω ^ 3) with hL
  have hL0 : 0 < L := div_pos hπ (by positivity)
  have hPbound : ∀ t, t1 ≤ t → t ≤ t1 + L → P t ≤ -π / 2 := by
    intro t ht1t htL
    have h := hPanti (Set.mem_Ici.2 le_rfl) ht1t ht1t
    simp only at h
    have : 2 * ω ^ 3 * (t - t1) ≤ 2 * ω ^ 3 * L :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hL' : 2 * ω ^ 3 * L = π / 2 := by rw [hL]; field_simp; ring
    have : P t1 ≤ -π := hP1
    nlinarith
  -- Y t + t₁ π t is antitone on [t₁, t₁ + L]
  have hYanti : AntitoneOn (fun t => y (t ^ 2) + t1 * π * t) (Icc t1 (t1 + L)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      ((cont_Y y φ hy).add (continuous_const.mul continuous_id)).continuousOn ?_ ?_
    · intro t ht
      rw [interior_Icc] at ht
      exact ((deriv_Y y φ hy (ht1.trans ht.1)).add
        ((hasDerivAt_id' t).const_mul (t1 * π))).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have htp : 0 < t := ht1.trans ht.1
      have hd : HasDerivAt (fun t => y (t ^ 2) + t1 * π * t) (2 * t * φ (t ^ 2) + t1 * π * 1) t :=
        (deriv_Y y φ hy htp).add ((hasDerivAt_id' t).const_mul (t1 * π))
      rw [hd.deriv]
      have hPt : φ (t ^ 2) ≤ -π / 2 := hPbound t ht.1.le ht.2.le
      nlinarith [ht.1]
  have hend := hYanti ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
  simp only at hend
  have hY1 : y (t1 ^ 2) ≤ ω ^ 2 := by
    have h := Real.sq_sqrt (hpos (t1 ^ 2) (sq_nonneg t1)).le
    have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hW1 2
    linarith
  have hkey : ω ^ 2 < t1 * π * L := by
    rw [hL, show t1 * π * (π / (4 * ω ^ 3)) = t1 * π ^ 2 / (4 * ω ^ 3) by ring,
      lt_div_iff₀ (by positivity)]
    nlinarith
  have := hpos ((t1 + L) ^ 2) (sq_nonneg _)
  nlinarith

end Work.Math.TFReduce
