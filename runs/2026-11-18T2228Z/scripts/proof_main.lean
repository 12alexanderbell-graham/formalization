by
  obtain ⟨W, Φ, hw, hφ0, hφ, h0⟩ := Checked.Math.BEGlobalExists.exists_global
  obtain ⟨ζ, hmono, htop, hz0lo, hz0hi, hl0lo, hl0hi, hmax0, hmin, hmax, hband, hlim, hinc0, hdec,
    hinc⟩ := Checked.Math.GelfandExtrema.gelfand_extrema W Φ hw hφ0 hφ h0
  obtain ⟨hl1lo, hl1hi, hl2lo, hl2hi⟩ :=
    Checked.Math.GLamBands.bands W Φ hw hφ0 hφ h0 ζ hmono hz0lo hz0hi hinc0 hdec hinc
  set Λ : ℝ → ℝ := fun s => s ^ 2 * Real.exp (W s) with hΛ
  have cW : ContinuousOn W (Ici 0) := fun t ht => (hw t ht).continuousWithinAt
  have cΛ : ContinuousOn Λ (Ici 0) := (continuousOn_id.pow 2).mul cW.rexp
  have Λ0 : Λ 0 = 0 := by simp [hΛ]
  have hz0 : 0 < ζ 0 := by norm_num at hz0lo; linarith
  have Λpos : ∀ s, 0 < s → 0 < Λ s := fun s hs => by simp only [hΛ]; positivity
  have hzpos : ∀ k, 0 < ζ k := fun k => lt_of_lt_of_le hz0 (hmono.monotone (Nat.zero_le k))
  obtain ⟨cA, cB, cC, cD, cE, cF, cG, cH⟩ :=
    Checked.Math.BonnorEbertCountMain.count_abstract Λ ζ 2 two_pos cΛ Λ0 hmono hz0
      (Λpos _ (hzpos 1)) hmax0 hmin hmax hband hinc0 hdec hinc
  have key := fun lam (hl : 0 < lam) => cset_encard W Φ hw hφ0 hφ h0 lam hl
  have lpos : ∀ k, 0 < Λ (ζ k) := fun k => Λpos _ (hzpos k)
  refine ⟨fun k => Λ (ζ k), hl0lo, hl0hi, hl1lo, hl1hi, hl2lo, hl2hi, ?_, ?_, hband, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · refine strictAnti_nat_of_succ_lt fun k => ?_
    rcases k with _ | j
    · exact hmax0 (ζ 2) (hzpos 2).le (hmono.injective.ne (by norm_num))
    · have h := hmax j (ζ (2 * (j + 1) + 2))
        (hmono.monotone (by omega)) (hmono.injective.ne (by omega))
      simpa [show 2 * (j + 1 + 1) = 2 * (j + 1) + 2 by ring, show 2 * j + 2 = 2 * (j + 1) by ring]
        using h
  · refine strictMono_nat_of_lt_succ fun k => ?_
    have h2 := hmin k (ζ (2 * (k + 1) + 1)) (hmono.monotone (by omega))
      (hmono.injective.ne (by omega))
    exact h2
  · exact hlim.comp htop
  · intro lam hl
    exact (key lam (by linarith [lpos 0])).trans (cA lam hl)
  · exact (key _ (lpos 0)).trans cB
  · intro k lam h1 h2
    exact (key lam (by linarith [lpos (2 * k + 2)])).trans (cC k lam h1 h2)
  · intro k
    exact (key _ (lpos _)).trans (cD k)
  · intro lam hl h1
    exact (key lam hl).trans (cE lam hl h1)
  · intro k
    exact (key _ (lpos _)).trans (cF k)
  · intro k lam h1 h2
    exact (key lam (by linarith [lpos (2 * k + 1)])).trans (cG k lam h1 h2)
  · exact (key 2 two_pos).trans cH
