  -- the certified cells on [150, 2000]
  have h2000 : (2000 : ℝ) ≤ S := hS
  have sub2000 : Icc ((150 : ℚ) : ℝ) ((2000 : ℚ) : ℝ) ⊆ Icc 0 S := by
    intro x hx; push_cast at hx; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have k150u' : |U 150 - 2105111091 / 2000000000| ≤ 1 / 5000000 := by
    have := abs_le.1 k150u; rw [abs_le]; constructor <;> linarith [this.1, this.2]
  have k150v' : |V 150 - 2331774279 / 1250000000| ≤ 1 / 5000000 := by
    have := abs_le.1 k150v; rw [abs_le]; constructor <;> linarith [this.1, this.2]
  obtain ⟨c2inc, c2br, c2dec, k2u, k2v⟩ := Work.Math.BEH2Chain.chain (u := U) (v := V)
    (fun t ht => (dW t ⟨by linarith [ht.1], ht.2.trans h2000⟩).1.mono sub2000)
    (fun t ht => (dW t ⟨by linarith [ht.1], ht.2.trans h2000⟩).2.mono sub2000) k150u' k150v'
  -- the zero ξ₃ of g = 2U − V in the second bracket
  set A2 : ℝ := 14671 / 20 with hA2
  set B2 : ℝ := 73399 / 100 with hB2
  have hAB2 : A2 ≤ B2 := by norm_num [hA2, hB2]
  have hA150 : (150 : ℝ) ≤ A2 := by norm_num [hA2]
  have hB2000 : B2 ≤ 2000 := by norm_num [hB2]
  have subAB2 : Icc A2 B2 ⊆ Icc 7 S := Icc_subset_Icc (by linarith) (by linarith)
  have cg2 : ContinuousOn (fun s => 2 * U s - V s) (Icc A2 B2) :=
    ((continuousOn_const.mul cU).sub cV).mono subAB2
  have gA2 : 0 < 2 * U A2 - V A2 := c2inc A2 ⟨hA150, le_rfl⟩
  have gB2 : 2 * U B2 - V B2 < 0 := c2dec B2 ⟨le_rfl, hB2000⟩
  obtain ⟨ξ₃, hξ₃, hg3⟩ := intermediate_value_Icc' hAB2 cg2 ⟨gB2.le, gA2.le⟩
  have ganti : StrictAntiOn (fun s => 2 * U s - V s) (Icc A2 B2) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc A2 B2) cg2
    intro x hx
    rw [interior_Icc] at hx
    have hx7 : x ∈ Ioo (7 : ℝ) S := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    obtain ⟨d1, d2⟩ := dA x hx7
    have hd : HasDerivAt (fun s => 2 * U s - V s)
        (2 * (U x * (3 - U x - V x) / x) - V x * (U x - 1) / x) x := (d1.const_mul 2).sub d2
    rw [hd.deriv]
    have hG := (c2br x ⟨hx.1.le, hx.2.le⟩).1
    have hx0 : 0 < x := by linarith [hx.1]
    have e : 2 * (U x * (3 - U x - V x) / x) - V x * (U x - 1) / x =
        (6 * U x - 2 * U x ^ 2 - 3 * (U x * V x) + V x) / x := by field_simp; ring
    rw [e]; exact div_neg_of_neg_of_pos hG hx0
  have ξ3a : A2 ≤ ξ₃ := hξ₃.1
  have ξ3b : ξ₃ ≤ B2 := hξ₃.2
  have ξ23 : ξ₂ < ξ₃ := by linarith
  have gpos2 : ∀ s ∈ Icc ξ₂ ξ₃, s ≠ ξ₂ → s ≠ ξ₃ → 0 < 2 * U s - V s := by
    intro s hs h2 h3
    rcases le_or_gt s 150 with h | h
    · exact gpos s ⟨hs.1, h⟩ h2
    · rcases le_or_gt s A2 with h' | h'
      · exact c2inc s ⟨h.le, h'⟩
      · have hlt : s < ξ₃ := lt_of_le_of_ne hs.2 h3
        have := ganti ⟨h'.le, by linarith⟩ hξ₃ hlt
        simp only at this hg3; linarith
  have gneg2 : ∀ s ∈ Icc ξ₃ 2000, s ≠ ξ₃ → 2 * U s - V s < 0 := by
    intro s hs h3
    rcases le_or_gt B2 s with h | h
    · exact c2dec s ⟨h, hs.2⟩
    · have hlt : ξ₃ < s := lt_of_le_of_ne hs.1 (Ne.symm h3)
      have := ganti hξ₃ ⟨by linarith, h.le⟩ hlt
      simp only at this hg3; linarith
  have Pmono2 : StrictMonoOn (fun s => U s * V s ^ 3) (Icc ξ₂ ξ₃) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc ξ₂ ξ₃) (cP.mono (Icc_subset_Icc ξ7.le (by linarith)))
    intro x hx
    rw [interior_Icc] at hx
    have hxS : x ∈ Ioo (7 : ℝ) S := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    rw [(dP x hxS).deriv]
    have hg := gpos2 x ⟨hx.1.le, hx.2.le⟩ hx.1.ne' hx.2.ne
    have hu := Upos x (Ioo_subset_Icc_self hxS)
    have hv := Vpos x (Ioo_subset_Icc_self hxS)
    have hx0 : 0 < x := by linarith [hx.1]
    positivity
  have Panti2 : StrictAntiOn (fun s => U s * V s ^ 3) (Icc ξ₃ 2000) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc ξ₃ 2000)
      (cP.mono (Icc_subset_Icc (by linarith) h2000))
    intro x hx
    rw [interior_Icc] at hx
    have hxS : x ∈ Ioo (7 : ℝ) S := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    rw [(dP x hxS).deriv]
    have hg := gneg2 x ⟨hx.1.le, hx.2.le⟩ hx.1.ne'
    have hu := Upos x (Ioo_subset_Icc_self hxS)
    have hv := Vpos x (Ioo_subset_Icc_self hxS)
    have hx0 : 0 < x := by linarith [hx.1]
    have : 0 < U x * V x ^ 3 := by positivity
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg this hg) hx0
  -- the state at ξ₃: v = 2u, u in the bracket window
  obtain ⟨-, vb1, vb2⟩ := c2br ξ₃ hξ₃
  have hVξ3 : V ξ₃ = 2 * U ξ₃ := by simp only at hg3; linarith
  have ξ3I : ξ₃ ∈ Icc (7 : ℝ) S := ⟨by linarith, by linarith⟩
  have ξ30 : 0 < ξ₃ := by linarith
  obtain ⟨Mξ3, Mξ3pos⟩ := mass_sq (w := w) ξ30 (φneg ξ₃ ξ3I)
  have hP83 : U ξ₃ * V ξ₃ ^ 3 = 8 * U ξ₃ ^ 4 := by rw [hVξ3]; ring
  have hMξ3 : M ξ₃ ^ 2 * (4 * Real.pi) = 8 * U ξ₃ ^ 4 := by
    rw [← hP83]; exact Mξ3
  obtain ⟨M3lo, M3hi⟩ := win_M hMξ3 Mξ3pos vb1 vb2
  -- the density contrast at ξ₃
  have hUV3 : U ξ₃ * V ξ₃ = ξ₃ ^ 2 * Real.exp (w ξ₃) := by
    have hp0 : φ ξ₃ ≠ 0 := (φneg ξ₃ ξ3I).ne
    simp only [hU, hV]; field_simp
  have hu30 : (0 : ℝ) < U ξ₃ := Upos ξ₃ ξ3I
  have hcon3 : Real.exp (-w ξ₃) = ξ₃ ^ 2 / (2 * U ξ₃ ^ 2) := by
    have h2 : U ξ₃ * V ξ₃ = 2 * U ξ₃ ^ 2 := by rw [hVξ3]; ring
    rw [hUV3] at h2
    have hE : Real.exp (w ξ₃) = 2 * U ξ₃ ^ 2 / ξ₃ ^ 2 := by
      rw [eq_div_iff (by positivity)]; linarith
    rw [Real.exp_neg, hE]; field_simp
  have hAξ3 : (14671 / 20 : ℝ) ≤ ξ₃ := ξ3a
  have hBξ3 : ξ₃ ≤ 73399 / 100 := ξ3b
  obtain ⟨C3lo, C3hi⟩ := win_C hu30 hAξ3 hBξ3 vb1 vb2
  rw [← hcon3] at C3lo C3hi
  -- beyond 2000: Volterra's function from above
  have I2000 : (2000 : ℝ) ∈ Icc 150 S := ⟨by norm_num, h2000⟩
  have P2000 : ∀ s ∈ Icc (2000 : ℝ) S, U s * V s ^ 3 < 865 / 100 := by
    intro s hs
    have hVs := VfA I2000 ⟨by linarith [hs.1], hs.2⟩ hs.1
    have k1 := abs_le.1 k2u
    have k2 := abs_le.1 k2v
    have hsI : s ∈ Icc (7 : ℝ) S := ⟨by linarith [hs.1], hs.2⟩
    exact Work.Math.BEH2Tail.uv_upper (Upos s hsI) (Vpos s hsI) (by linarith [k1.1]) (by linarith [k1.2])
      (by linarith [k2.1]) (by linarith [k2.2]) hVs
  have Pξ3gt : 865 / 100 < U ξ₃ * V ξ₃ ^ 3 := P_gt Mξ3 M3lo
  have hmax2 : ∀ s ∈ Icc ξ₂ S, s ≠ ξ₃ → M s < M ξ₃ := by
    intro s hs hne
    have sI : s ∈ Icc (7 : ℝ) S := ⟨by linarith [hs.1], hs.2⟩
    have hs0 : 0 < s := by linarith [sI.1]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact mass_lt hs0 (φneg s sI) ξ30 (φneg ξ₃ ξ3I)
        (Pmono2 ⟨hs.1, hlt.le⟩ ⟨ξ23.le, le_rfl⟩ hlt)
    · rcases le_or_gt s 2000 with h1 | h1
      · exact mass_lt hs0 (φneg s sI) ξ30 (φneg ξ₃ ξ3I)
          (Panti2 ⟨le_rfl, by linarith⟩ ⟨hgt.le, h1⟩ hgt)
      · exact mass_lt hs0 (φneg s sI) ξ30 (φneg ξ₃ ξ3I)
          (lt_trans (P2000 s ⟨h1.le, hs.2⟩) Pξ3gt)
  refine ⟨ξ, ξ₂, ξ₃, hξ1, hξ2, by norm_num at hAξ ⊢; linarith, by norm_num at hBξ ⊢; linarith,
    by norm_num at hAξ3 ⊢; linarith, by norm_num at hBξ3 ⊢; linarith,
    hmax, hmin, hmax2, M3lo, M3hi, C3lo, C3hi⟩
