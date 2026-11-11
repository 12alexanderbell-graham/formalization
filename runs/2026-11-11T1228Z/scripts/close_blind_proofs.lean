-- PROOF blind_rev_window
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, hb, hdec, w1, w2⟩ :=
    Work.FalknerSkan.Neg1988Rev.fs_neg1988_reversed
  obtain ⟨S, E1, E2⟩ := transfer hf hp hq hf0 hp0 hlim
  refine ⟨f, S, fun η hη => ?_, superExp_of E1 E2 hdec, ?_, ?_⟩
  · rw [E1 η hη, abs_le]; exact hb η hη
  · rw [E2 0 (mem_Ici.2 le_rfl)]; exact w1
  · rw [E2 0 (mem_Ici.2 le_rfl)]; exact w2
-- END
-- PROOF blind_rev_two
  obtain ⟨f, p, q, f₂, p₂, q₂, a1, a2, a3, b1, b2, b3, a4, a5, b4, b5, a6, b6, a7, b7, a8, b8, hne⟩ :=
    Work.FalknerSkan.Neg1988Rev.fs_neg1988_two_decay
  obtain ⟨S, E1, E2⟩ := transfer a1 a2 a3 a4 a5 a6
  obtain ⟨S₂, F1, F2⟩ := transfer b1 b2 b3 b4 b5 b6
  refine ⟨f, f₂, S, S₂, fun η hη => ?_, fun η hη => ?_, superExp_of E1 E2 a8, superExp_of F1 F2 b8, ?_⟩
  · rw [E1 η hη, abs_le]; exact a7 η hη
  · rw [F1 η hη, abs_le]; exact b7 η hη
  · rw [E2 0 (mem_Ici.2 le_rfl), F2 0 (mem_Ici.2 le_rfl)]; exact hne
-- END
-- PROOF blind_rev_printed
  have hu : UniqueDiffOn ℝ (Ici (0 : ℝ)) := uniqueDiffOn_Ici 0
  have hC := hf.1
  have C1 : ContDiffOn ℝ 2 (d1 f) (Ici 0) := hC.derivWithin hu (by norm_num)
  have C2 : ContDiffOn ℝ 1 (d2 f) (Ici 0) := C1.derivWithin hu (by norm_num)
  obtain ⟨η, hη, h⟩ := Work.FalknerSkan.Neg1988Rev.fs_neg1988_printed_reversed_overshoots f (d1 f) (d2 f)
    (fun η hη => ((hC.differentiableOn (by norm_num)) η hη).hasDerivWithinAt)
    (fun η hη => ((C1.differentiableOn (by norm_num)) η hη).hasDerivWithinAt)
    (fun η hη => by
      refine ((C2.differentiableOn (by norm_num)) η hη).hasDerivWithinAt.congr_deriv ?_
      have := hf.2 η hη
      rw [β_eq] at this
      change d3 f η = _
      linarith) hw.1 hw.2 h2
  exact ⟨η, hη, h⟩
-- END
