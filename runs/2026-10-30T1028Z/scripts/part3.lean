lemma alg5 (H B A E x C : ℝ) (hw : A + E ≠ 0) (hab : A * B = 1 + x ^ 5 * C) :
    H * (B - (A + E)⁻¹) = H * ((x ^ 5 * C + E * B) * (A + E)⁻¹) := by
  field_simp
  linear_combination H * hab

/-- **Headline.** Luminosity distance to fifth order in `y` for every curvature `K`
and every scale factor that is `C⁵` at `t₀` with `a(t₀) ≠ 0`, `H₀ ≠ 0`. -/
theorem lumDist_y_fifth_order (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 5 a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0) :
    (fun t => remK correctD2y correctD3y correctD4y K a t₀ t) =o[𝓝 t₀]
      (fun t => yred a t₀ t ^ 5) := by
  set a₀ := a t₀ with ha₀
  set H := hubble a t₀ with hHdef
  set q := decel a t₀ with hq
  set j := cosmoCoeff 3 a t₀ with hj
  set s := cosmoCoeff 4 a t₀ with hs
  set l := cosmoCoeff 5 a t₀ with hl
  set k := K / (a₀ * H) ^ 2 with hk
  have hΩ : omega0 K a t₀ = 1 + k := by
    show 1 + K / (H ^ 2 * a₀ ^ 2) = 1 + K / (a₀ * H) ^ 2
    ring
  have hd : DifferentiableAt ℝ a t₀ := ha.differentiableAt (by norm_num)
  -- a ball on which `a` is `C⁵` and nonzero
  obtain ⟨U, hU, hcd⟩ := ha.contDiffOn le_rfl (by simp)
  have hne : {t | a t ≠ 0} ∈ 𝓝 t₀ := hd.continuousAt.eventually_ne ha0
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hU hne)
  set Bl := Metric.ball t₀ δ with hBl
  have hopen : IsOpen Bl := Metric.isOpen_ball
  have hmem : t₀ ∈ Bl := Metric.mem_ball_self hδ
  have hBl_nhds : Bl ∈ 𝓝 t₀ := hopen.mem_nhds hmem
  have hcdB : ContDiffOn ℝ 5 a Bl := hcd.mono fun t ht => (hball ht).1
  have hnz : ∀ t ∈ Bl, a t ≠ 0 := fun t ht => (hball ht).2
  have hcont : ContinuousOn a Bl := hcdB.continuousOn
  -- Taylor's theorem
  have hT := taylor_isLittleO (convex_ball t₀ δ) hmem hcdB
  rw [hopen.nhdsWithin_eq hmem] at hT
  have hid : ∀ n, iteratedDerivWithin n a Bl t₀ = iteratedDeriv n a t₀ :=
    fun n => iteratedDerivWithin_of_isOpen hopen hmem
  have d1 : iteratedDeriv 1 a t₀ = H * a₀ := by
    rw [iteratedDeriv_one]; simp only [hHdef, hubble]; rw [← ha₀]; field_simp
  have hd1 : deriv a t₀ ≠ 0 := by
    intro h0; apply hH; rw [hHdef]; simp [hubble, h0]
  have d2 : iteratedDeriv 2 a t₀ = -q * H ^ 2 * a₀ := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    simp only [hq, decel, hHdef, hubble]; rw [← ha₀]; field_simp
  have dk : ∀ n, iteratedDeriv n a t₀ = cosmoCoeff n a t₀ * (a₀ * H ^ n) := by
    intro n; simp only [cosmoCoeff, hHdef]
    rw [div_mul_cancel₀]; exact mul_ne_zero ha0 (pow_ne_zero _ hH)
  have hpoly : ∀ t, taylorWithinEval a 5 Bl t₀ t = a₀ * CCS.Apoly q j s l (H * (t₀ - t)) := by
    intro t
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hid, smul_eq_mul]
    rw [iteratedDeriv_zero, d1, d2, dk 3, dk 4, dk 5]
    simp only [CCS.Apoly, Nat.factorial, Nat.cast_ofNat]
    push_cast
    ring
  set X : ℝ → ℝ := fun t => H * (t₀ - t) with hX
  set E : ℝ → ℝ := fun t => a t / a₀ - CCS.Apoly q j s l (X t) with hE
  have hXc : Continuous X := by fun_prop
  have hXt : Tendsto X (𝓝 t₀) (𝓝 0) := by simpa [hX] using hXc.tendsto t₀
  have htX : ∀ n : ℕ, (fun t => (t - t₀) ^ n) =O[𝓝 t₀] fun t => X t ^ n := by
    intro n
    have : (fun t => t - t₀) =O[𝓝 t₀] X := by
      refine IsBigO.of_bound (‖H‖⁻¹) (Eventually.of_forall fun t => ?_)
      simp only [hX, norm_mul]
      rw [← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.2 hH), one_mul, ← norm_neg]; ring_nf; rfl
    exact this.pow n
  have hXt' : ∀ n : ℕ, (fun t => X t ^ n) =O[𝓝 t₀] fun t => (t - t₀) ^ n := by
    intro n
    have : X =O[𝓝 t₀] (fun t => t - t₀) := by
      refine IsBigO.of_bound (‖H‖) (Eventually.of_forall fun t => ?_)
      simp only [hX, norm_mul, ← norm_neg (t₀ - t)]; ring_nf; rfl
    exact this.pow n
  have hEo : E =o[𝓝 t₀] fun t => X t ^ 5 := by
    have h1 : E = fun t => a₀⁻¹ * (a t - taylorWithinEval a 5 Bl t₀ t) := by
      funext t; simp only [hE, hpoly, hX]; field_simp
    rw [h1]
    exact (hT.const_mul_left a₀⁻¹).trans_isBigO (htX 5)
  have hE0 : Tendsto E (𝓝 t₀) (𝓝 0) := by
    have : Tendsto (fun t => X t ^ 5) (𝓝 t₀) (𝓝 0) := by simpa using hXt.pow 5
    exact hEo.trans_tendsto this
  have hwE : ∀ t, a t / a₀ = CCS.Apoly q j s l (X t) + E t := fun t => by simp only [hE]; ring
  have hw1A : Tendsto (fun t => CCS.Apoly q j s l (X t) + E t) (𝓝 t₀) (𝓝 1) := by
    have h := (((cont_A q j s l).tendsto 0).comp hXt).add hE0
    rw [show CCS.Apoly q j s l 0 + 0 = 1 by simp [CCS.Apoly]] at h
    exact h
  have hwinvA : (fun t => (CCS.Apoly q j s l (X t) + E t)⁻¹) =O[𝓝 t₀] (fun _ => (1 : ℝ)) :=
    (hw1A.inv₀ one_ne_zero).isBigO_one ℝ
  have hw1 : Tendsto (fun t => a t / a₀) (𝓝 t₀) (𝓝 1) := hw1A.congr fun t => (hwE t).symm
  have hwinv : (fun t => (a t / a₀)⁻¹) =O[𝓝 t₀] (fun _ => (1 : ℝ)) :=
    (hw1.inv₀ one_ne_zero).isBigO_one ℝ
  -- comoving distance: u = a₀ H χ = P5(X) + o(X⁵)
  set u : ℝ → ℝ := fun t => a₀ * H * comoving a t₀ t with hu
  set R : ℝ → ℝ := fun t => u t - P5 q j s l k (X t) with hR
  set R' : ℝ → ℝ := fun t => H * (B4 q j s l k (X t) - a₀ / a t) with hR'
  have hfc : ContinuousOn (fun s => 1 / a s) Bl := continuousOn_const.div hcont hnz
  have hderR : ∀ t ∈ Bl, HasDerivAt R (R' t) t := by
    intro t ht
    have hsub : Set.uIcc t t₀ ⊆ Bl := (convex_ball t₀ δ).ordConnected.uIcc_subset ht hmem
    have hχ : HasDerivAt (comoving a t₀) (-(1 / a t)) t :=
      intervalIntegral.integral_hasDerivAt_left ((hfc.mono hsub).intervalIntegrable)
        (hfc.stronglyMeasurableAtFilter hopen t ht) (hfc.continuousAt (hopen.mem_nhds ht))
    have hXd : HasDerivAt X (-H) t := by
      simpa using ((hasDerivAt_id t).const_sub t₀).const_mul H
    have hP := (hasDerivAt_P5 q j s l k (X t)).comp t hXd
    have := (hχ.const_mul (a₀ * H)).sub hP
    have e : R' t = a₀ * H * -(1 / a t) - B4 q j s l k (X t) * -H := by
      show H * (B4 q j s l k (X t) - a₀ / a t) = _
      ring
    rw [e]; exact this
  have hR0 : R t₀ = 0 := by simp [hR, hu, comoving, hX, P5]
  have hR'o : R' =o[𝓝 t₀] fun t => (t - t₀) ^ 4 := by
    have e1 : ∀ t ∈ Bl, R' t = H * ((X t ^ 5 * C5 q j s l k (X t) + E t * B4 q j s l k (X t))
        * (CCS.Apoly q j s l (X t) + E t)⁻¹) := by
      intro t ht
      have hw : CCS.Apoly q j s l (X t) + E t ≠ 0 := by
        rw [← hwE]; exact div_ne_zero (hnz t ht) ha0
      have ha' : a₀ / a t = (CCS.Apoly q j s l (X t) + E t)⁻¹ := by rw [← hwE, inv_div]
      show H * (B4 q j s l k (X t) - a₀ / a t) = _
      rw [ha']
      exact alg5 H _ _ _ _ _ hw (idAB q j s l k (X t))
    have b1 : (fun t => X t ^ 5 * C5 q j s l k (X t)) =o[𝓝 t₀] fun t => X t ^ 4 :=
      pow_succ_mul_isLittleO hXt 4 _ (CCS.bdd hXt _ (cont_C5 q j s l k))
    have hX54 : (fun t => X t ^ 5) =o[𝓝 t₀] fun t => X t ^ 4 := by
      simpa using pow_succ_mul_isLittleO hXt 4 (fun _ => (1 : ℝ)) (isBigO_refl _ _)
    have b2 : (fun t => E t * B4 q j s l k (X t)) =o[𝓝 t₀] fun t => X t ^ 4 := by
      simpa using (hEo.trans hX54).mul_isBigO (CCS.bdd hXt _ (cont_B4 q j s l k))
    have b3 := (((b1.add b2).mul_isBigO hwinvA).const_mul_left H)
    simp only [mul_one] at b3
    exact (b3.congr' (Filter.eventually_of_mem hBl_nhds fun t ht => (e1 t ht).symm)
      EventuallyEq.rfl).trans_isBigO (hXt' 4)
  have hRo : R =o[𝓝 t₀] fun t => X t ^ 5 :=
    (littleO_of_hasDerivAt hR0 (Filter.eventually_of_mem hBl_nhds hderR) hR'o).trans_isBigO
      (htX 5)
  have au0 : (fun t => u t - P5 q j s l k (X t)) =o[𝓝 t₀] fun t => X t ^ 5 := hRo
  have au1 : (fun t => u t ^ 1 - P5 q j s l k (X t)) =o[𝓝 t₀] fun t => X t ^ 5 := by
    simpa only [pow_one] using au0
  have au2 := approx_pow (n := 1) hXt (cont_P5 q j s l k) (cont_P5 q j s l k)
    (cont_WM2 q j s l k) (idM2 q j s l k) au0 au1
  have au3 := approx_pow (n := 2) hXt (cont_P5 q j s l k) (cont_M2 q j s l k)
    (cont_WM3 q j s l k) (idM3 q j s l k) au0 au2
  have au4 := approx_pow (n := 3) hXt (cont_P5 q j s l k) (cont_M3 q j s l k)
    (cont_WM4 q j s l k) (idM4 q j s l k) au0 au3
  have au5 := approx_pow (n := 4) hXt (cont_P5 q j s l k) (cont_M4 q j s l k)
    (cont_WM5 q j s l k) (idM5 q j s l k) au0 au4
  -- χ = O(X), so the transverse expansion transfers
  have hX5X : (fun t => X t ^ 5) =O[𝓝 t₀] X := by
    have h := (isBigO_refl X (𝓝 t₀)).mul ((hXt.pow 4).isBigO_one ℝ)
    refine h.congr' (Eventually.of_forall fun t => ?_) (Eventually.of_forall fun t => ?_)
    · simp only; ring
    · simp
  have huX : u =O[𝓝 t₀] X := by
    have h1 : (fun t => P5 q j s l k (X t)) =O[𝓝 t₀] X := by
      have := (isBigO_refl X (𝓝 t₀)).mul (CCS.bdd hXt _ (cont_P5q q j s l k))
      refine this.congr' (Eventually.of_forall fun t => ?_) (Eventually.of_forall fun t => ?_)
      · simp only [idP]
      · simp
    have h2 : R =O[𝓝 t₀] X := hRo.isBigO.trans hX5X
    refine (h2.add h1).congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
    simp only [hR]; ring
  have haH : a₀ * H ≠ 0 := mul_ne_zero ha0 hH
  have hχX : (fun t => comoving a t₀ t) =O[𝓝 t₀] X := by
    have := huX.const_mul_left (a₀ * H)⁻¹
    refine this.congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
    simp only [hu]; field_simp
  have hχ0 : Tendsto (fun t => comoving a t₀ t) (𝓝 t₀) (𝓝 0) := hχX.trans_tendsto hXt
  have hS := ((transverse_expansion K).comp_tendsto hχ0).const_mul_left (a₀ * H)
  have hS' := hS.trans_isBigO (hχX.pow 5)
  have aSig : (fun t => a₀ * H * transverse K (comoving a t₀ t) - Fpoly q j s l k (X t))
      =o[𝓝 t₀] fun t => X t ^ 5 := by
    have h := ((hS'.add au0).sub (au3.const_mul_left (k / 6))).add
      (au5.const_mul_left (k ^ 2 / 120))
    refine h.congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
    simp only [Function.comp, hu, Fpoly, hk]
    field_simp
    ring
  -- y = 1 − a/a₀ ≈ N1(X), and its powers
  have hyE : ∀ t ∈ Bl, yred a t₀ t = 1 - a t / a₀ := fun t ht => by
    have := hnz t ht
    simp only [yred, redshift]
    field_simp
    ring
  have ay1 : (fun t => yred a t₀ t - N1 q j s l k (X t)) =o[𝓝 t₀] fun t => X t ^ 5 := by
    refine hEo.neg_left.congr' (Filter.eventually_of_mem hBl_nhds fun t ht => ?_)
      EventuallyEq.rfl
    rw [hyE t ht]; simp only [hE, N1]; ring
  have ay1' : (fun t => yred a t₀ t ^ 1 - N1 q j s l k (X t)) =o[𝓝 t₀] fun t => X t ^ 5 := by
    simpa only [pow_one] using ay1
  have ay2 := approx_pow (n := 1) hXt (cont_N1 q j s l k) (cont_N1 q j s l k)
    (cont_WN2 q j s l k) (idN2 q j s l k) ay1 ay1'
  have ay3 := approx_pow (n := 2) hXt (cont_N1 q j s l k) (cont_N2 q j s l k)
    (cont_WN3 q j s l k) (idN3 q j s l k) ay1 ay2
  have ay4 := approx_pow (n := 3) hXt (cont_N1 q j s l k) (cont_N3 q j s l k)
    (cont_WN4 q j s l k) (idN4 q j s l k) ay1 ay3
  have ay5 := approx_pow (n := 4) hXt (cont_N1 q j s l k) (cont_N4 q j s l k)
    (cont_WN5 q j s l k) (idN5 q j s l k) ay1 ay4
  have aS : (fun t => seriesY4 q (correctD2y q j (1 + k)) (correctD3y q j s (1 + k))
      (correctD4y q j s l (1 + k)) (yred a t₀ t) - Spoly q j s l k (X t))
      =o[𝓝 t₀] fun t => X t ^ 5 := by
    have h := ((((ay1.add (ay2.const_mul_left (D1y q))).add
      (ay3.const_mul_left (correctD2y q j (1 + k)))).add
      (ay4.const_mul_left (correctD3y q j s (1 + k)))).add
      (ay5.const_mul_left (correctD4y q j s l (1 + k))))
    refine h.congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
    simp only [seriesY4, Spoly]; ring
  have aw : (fun t => a t / a₀ - CCS.Apoly q j s l (X t)) =o[𝓝 t₀] fun t => X t ^ 5 := hEo
  have awS := approx_mul hXt (cont_A q j s l) (cont_Spoly q j s l k) (cont_Wf q j s l k)
    (idFin q j s l k) aw aS
  have hN := (aSig.sub awS).mul_isBigO hwinv
  simp only [mul_one] at hN
  have e2 : ∀ t ∈ Bl, remK correctD2y correctD3y correctD4y K a t₀ t =
      ((a₀ * H * transverse K (comoving a t₀ t) - Fpoly q j s l k (X t)) -
        (a t / a₀ * seriesY4 q (correctD2y q j (1 + k)) (correctD3y q j s (1 + k))
          (correctD4y q j s l (1 + k)) (yred a t₀ t) - Fpoly q j s l k (X t)))
        * (a t / a₀)⁻¹ := by
    intro t ht
    have := hnz t ht
    show H * (a₀ * (1 + (a₀ / a t - 1)) * transverse K (comoving a t₀ t)) -
      seriesY4 q (correctD2y q j (omega0 K a t₀)) (correctD3y q j s (omega0 K a t₀))
        (correctD4y q j s l (omega0 K a t₀)) (yred a t₀ t) = _
    rw [hΩ]
    field_simp
    ring
  have hfin := hN.congr' (Filter.eventually_of_mem hBl_nhds fun t ht => (e2 t ht).symm)
    EventuallyEq.rfl
  have hXy : X =O[𝓝 t₀] fun t => yred a t₀ t := by
    have : X =O[𝓝 t₀] (fun t => t - t₀) := by simpa using hXt' 1
    exact this.trans (sub_isBigO_yred a t₀ hd ha0 hH)
  exact hfin.trans_isBigO (hXy.pow 5)
