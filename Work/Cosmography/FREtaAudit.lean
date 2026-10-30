import Work.Cosmography.FREta
import Work.Cosmography.FREtaBlind

/-!
# C14 audit: blind restatement closed in Lean (run 2026-10-30T1628Z)

The blind restater (`Work.Cosmography.FREtaBlind`, written without seeing `FREta`) built the
ratios from (11.21), (11.23), (11.24) with the printed `R` (11.31) and formalized "first order in
`ε`" as `η(ε) − cε = o(ε)`. Here: its ratios agree with ours wherever its `R ≠ 0` (so near
`ε = 0`), its corrected statements are proved from ours, and its readings of the printed claims
(11.42)–(11.45) are refuted.

Earliest divergence: the numerator of (11.43). The blind read `6[((81Ω − 110)Ω + 40)Ω + 16]`;
we read `6[(81Ω − 110)Ω + 40]Ω + 16`. The typeset bracket closes after `+ 40` (crop
`runs/2026-10-30T1232Z/screen_secXI/cand5_eq11.42-45_eta.png`), and only our reading reproduces the
printed `4ε` at Ω = 0.041 (4.02; the blind reading gives 17.0). Classified Translation (blind),
resolved by the source text. Both readings are refuted.
-/

namespace Work.Cosmography.FREtaAudit

open Filter Topology Asymptotics Checked.Cosmography.FRCosmo
open Work.Cosmography

lemma fam_eq (Ω ε : ℝ) :
    FREtaBlind.qL Ω * (1 + ε) = FREta.qL Ω * (1 + ε) ∧ FREtaBlind.jL Ω * (1 + ε) = FREta.jL * (1 + ε)
      ∧ FREtaBlind.sL Ω * (1 + ε) = FREta.sL Ω * (1 + ε)
      ∧ FREtaBlind.lL Ω * (1 + ε) = FREta.lL Ω * (1 + ε) := by
  unfold FREtaBlind.qL FREta.qL FREtaBlind.jL FREta.jL FREtaBlind.sL FREta.sL FREtaBlind.lL FREta.lL
  refine ⟨by ring, by ring, by ring, by ring⟩

/-- Blind's printed `R` along the family. -/
noncomputable def Rfam (Ω ε : ℝ) : ℝ :=
  printedR (FREta.qL Ω * (1 + ε)) (FREta.jL * (1 + ε)) (FREta.sL Ω * (1 + ε)) (FREta.lL Ω * (1 + ε))

lemma Rfam_cont (Ω : ℝ) : Continuous (Rfam Ω) := by
  unfold Rfam printedR FREta.qL FREta.jL FREta.sL FREta.lL; fun_prop

lemma blind_eta20_eq {H Ω ε : ℝ} (hH : H ≠ 0) (hR : Rfam Ω ε ≠ 0) :
    FREtaBlind.eta20 H Ω ε = FREta.eta20 Ω ε := by
  obtain ⟨e1, e2, e3, e4⟩ := fam_eq Ω ε
  unfold FREtaBlind.eta20 FREtaBlind.F0 FREtaBlind.F2 FREta.eta20 FREta.eta20Of
  rw [e1, e2, e3, e4]
  unfold Rfam at hR
  generalize printedR (FREta.qL Ω * (1 + ε)) (FREta.jL * (1 + ε)) (FREta.sL Ω * (1 + ε))
    (FREta.lL Ω * (1 + ε)) = R at hR ⊢
  generalize P0 (FREta.qL Ω * (1 + ε)) (FREta.jL * (1 + ε)) (FREta.sL Ω * (1 + ε))
    (FREta.lL Ω * (1 + ε)) * Ω + Q0 (FREta.qL Ω * (1 + ε)) (FREta.jL * (1 + ε))
    (FREta.sL Ω * (1 + ε)) (FREta.lL Ω * (1 + ε)) = D
  generalize P2 (FREta.qL Ω * (1 + ε)) (FREta.jL * (1 + ε)) (FREta.sL Ω * (1 + ε)) * Ω
    + Q2 (FREta.qL Ω * (1 + ε)) (FREta.jL * (1 + ε)) (FREta.sL Ω * (1 + ε)) = N
  by_cases hD : D = 0
  · simp [hD]
  · field_simp
    ring

lemma blind_eta30_eq {H Ω ε : ℝ} (hH : H ≠ 0) (hR : Rfam Ω ε ≠ 0) :
    FREtaBlind.eta30 H Ω ε = FREta.eta30 Ω ε := by
  obtain ⟨e1, e2, e3, e4⟩ := fam_eq Ω ε
  unfold FREtaBlind.eta30 FREtaBlind.F0 FREtaBlind.F3 FREta.eta30 FREta.eta30Of
  rw [e1, e2, e3, e4]
  unfold Rfam at hR
  generalize printedR (FREta.qL Ω * (1 + ε)) (FREta.jL * (1 + ε)) (FREta.sL Ω * (1 + ε))
    (FREta.lL Ω * (1 + ε)) = R at hR ⊢
  generalize P0 (FREta.qL Ω * (1 + ε)) (FREta.jL * (1 + ε)) (FREta.sL Ω * (1 + ε))
    (FREta.lL Ω * (1 + ε)) * Ω + Q0 (FREta.qL Ω * (1 + ε)) (FREta.jL * (1 + ε))
    (FREta.sL Ω * (1 + ε)) (FREta.lL Ω * (1 + ε)) = D
  generalize P3 (FREta.qL Ω * (1 + ε)) (FREta.jL * (1 + ε)) (FREta.sL Ω * (1 + ε))
    (FREta.lL Ω * (1 + ε)) * Ω + Q3 (FREta.qL Ω * (1 + ε)) (FREta.jL * (1 + ε))
    (FREta.sL Ω * (1 + ε)) (FREta.lL Ω * (1 + ε)) = N
  generalize FREta.jL * (1 + ε) - FREta.qL Ω * (1 + ε) - 2 = J
  by_cases hD : D = 0
  · simp [hD]
  by_cases hJ : J = 0
  · simp [hJ]
  · field_simp
    ring

/-- First order (blind's sense) for a function with `f 0 = 0` is `HasDerivAt f c 0`. -/
lemma firstOrder_iff {f : ℝ → ℝ} {c : ℝ} (h0 : f 0 = 0) :
    FREtaBlind.FirstOrder f c ↔ HasDerivAt f c 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero, FREtaBlind.FirstOrder]
  simp only [zero_add, h0, sub_zero, smul_eq_mul, mul_comm c]

lemma eventually_R {Ω : ℝ} (hR : printedR (FREtaBlind.qL Ω) (FREtaBlind.jL Ω) (FREtaBlind.sL Ω)
    (FREtaBlind.lL Ω) ≠ 0) : ∀ᶠ ε in 𝓝 (0 : ℝ), Rfam Ω ε ≠ 0 := by
  refine (Rfam_cont Ω).continuousAt.eventually_ne ?_
  obtain ⟨e1, e2, e3, e4⟩ := fam_eq Ω 0
  simp only [add_zero, mul_one] at e1 e2 e3 e4
  unfold Rfam; simpa [e1, e2, e3, e4] using hR

lemma blind20_iff {H Ω c : ℝ} (hH : H ≠ 0) (h0 : 0 < Ω) (h1 : Ω < 1)
    (hR : printedR (FREtaBlind.qL Ω) (FREtaBlind.jL Ω) (FREtaBlind.sL Ω) (FREtaBlind.lL Ω) ≠ 0) :
    FREtaBlind.FirstOrder (FREtaBlind.eta20 H Ω) c ↔ HasDerivAt (FREta.eta20 Ω) c 0 := by
  rw [← firstOrder_iff (FREta.eta20_hasDerivAt h0 h1).1, FREtaBlind.FirstOrder,
    FREtaBlind.FirstOrder]
  refine isLittleO_congr ?_ EventuallyEq.rfl
  filter_upwards [eventually_R hR] with ε hε
  rw [blind_eta20_eq hH hε]

lemma blind30_iff {H Ω c : ℝ} (hH : H ≠ 0) (h0 : 0 < Ω) (h1 : Ω < 1)
    (hR : printedR (FREtaBlind.qL Ω) (FREtaBlind.jL Ω) (FREtaBlind.sL Ω) (FREtaBlind.lL Ω) ≠ 0) :
    FREtaBlind.FirstOrder (FREtaBlind.eta30 H Ω) c ↔ HasDerivAt (FREta.eta30 Ω) c 0 := by
  rw [← firstOrder_iff (FREta.eta30_hasDerivAt h0 h1).1, FREtaBlind.FirstOrder,
    FREtaBlind.FirstOrder]
  refine isLittleO_congr ?_ EventuallyEq.rfl
  filter_upwards [eventually_R hR] with ε hε
  rw [blind_eta30_eq hH hε]

lemma trueC20_eq (Ω : ℝ) : FREtaBlind.trueC20 Ω = FREta.correct20 Ω := by
  unfold FREtaBlind.trueC20 FREta.correct20; ring

theorem blind_eta20Corrected : FREtaBlind.Eta20Corrected := by
  intro H Ω hH h0 h1 hR
  rw [blind20_iff hH h0 h1 hR, trueC20_eq]
  exact (FREta.eta20_hasDerivAt h0 h1).2

theorem blind_eta30Corrected : FREtaBlind.Eta30Corrected := by
  intro H Ω hH h0 h1 hR
  rw [blind30_iff hH h0 h1 hR]
  exact (FREta.eta30_hasDerivAt h0 h1).2

lemma R041 : printedR (FREtaBlind.qL (41 / 1000)) (FREtaBlind.jL (41 / 1000))
    (FREtaBlind.sL (41 / 1000)) (FREtaBlind.lL (41 / 1000)) ≠ 0 := by
  unfold printedR FREtaBlind.qL FREtaBlind.jL FREtaBlind.sL FREtaBlind.lL; norm_num

lemma R250 : printedR (FREtaBlind.qL (1 / 4)) (FREtaBlind.jL (1 / 4))
    (FREtaBlind.sL (1 / 4)) (FREtaBlind.lL (1 / 4)) ≠ 0 := by
  unfold printedR FREtaBlind.qL FREtaBlind.jL FREtaBlind.sL FREtaBlind.lL; norm_num

lemma nd250 : FREtaBlind.NonDegenerate (1 / 4) := by
  refine ⟨by norm_num, by norm_num, R250, ?_, by unfold FREtaBlind.printedDen; norm_num⟩
  unfold P0 Q0 FREtaBlind.qL FREtaBlind.jL FREtaBlind.sL FREtaBlind.lL; norm_num

theorem blind_eta20Claim_false : ¬ FREtaBlind.Eta20Claim := by
  intro h
  have h' := (blind20_iff one_ne_zero (by norm_num) (by norm_num) R250).1 (h 1 (1 / 4) one_ne_zero nd250)
  exact FREta.printedEta20_false_at (Ω := 1 / 4) (by norm_num) (by norm_num)
    (by unfold FREta.printedDen; norm_num) (by norm_num)
    (by convert h' using 1
        unfold FREta.printed20 FREtaBlind.printedC20 FREta.printedDen FREtaBlind.printedDen; rfl)

theorem blind_eta30Claim_false : ¬ FREtaBlind.Eta30Claim := by
  intro h
  have h' := (blind30_iff one_ne_zero (by norm_num) (by norm_num) R250).1 (h 1 (1 / 4) one_ne_zero nd250)
  have := h'.unique (FREta.eta30_hasDerivAt (Ω := 1 / 4) (by norm_num) (by norm_num)).2
  unfold FREtaBlind.printedC30 FREtaBlind.printedDen FREta.correct30 at this
  norm_num at this

/-- The first-order coefficient (blind's sense) at the fiducial values is ours. -/
lemma coeff20 {Ω c : ℝ} (h0 : 0 < Ω) (h1 : Ω < 1)
    (hR : printedR (FREtaBlind.qL Ω) (FREtaBlind.jL Ω) (FREtaBlind.sL Ω) (FREtaBlind.lL Ω) ≠ 0)
    (h : FREtaBlind.FirstOrder (FREtaBlind.eta20 1 Ω) c) : c = FREta.correct20 Ω :=
  ((blind20_iff one_ne_zero h0 h1 hR).1 h).unique (FREta.eta20_hasDerivAt h0 h1).2

lemma coeff30 {Ω c : ℝ} (h0 : 0 < Ω) (h1 : Ω < 1)
    (hR : printedR (FREtaBlind.qL Ω) (FREtaBlind.jL Ω) (FREtaBlind.sL Ω) (FREtaBlind.lL Ω) ≠ 0)
    (h : FREtaBlind.FirstOrder (FREtaBlind.eta30 1 Ω) c) : c = FREta.correct30 Ω :=
  ((blind30_iff one_ne_zero h0 h1 hR).1 h).unique (FREta.eta30_hasDerivAt h0 h1).2

theorem blind_eta20Num041_false : ¬ FREtaBlind.Eta20Num041 := by
  rintro ⟨c, hc, h⟩
  have := coeff20 (by norm_num) (by norm_num) R041 (h 1 one_ne_zero)
  obtain ⟨⟨a, b⟩, -⟩ := FREta.eta_numbers
  rw [abs_le] at hc; subst this; norm_num at a b hc; linarith [hc.1, hc.2]

theorem blind_eta20Num250_false : ¬ FREtaBlind.Eta20Num250 := by
  rintro ⟨c, hc, h⟩
  have := coeff20 (by norm_num) (by norm_num) R250 (h 1 one_ne_zero)
  obtain ⟨-, ⟨a, b⟩, -⟩ := FREta.eta_numbers
  rw [abs_le] at hc; subst this; norm_num at a b hc; linarith [hc.1, hc.2]

theorem blind_eta30Num041_false : ¬ FREtaBlind.Eta30Num041 := by
  rintro ⟨c, hc, h⟩
  have := coeff30 (by norm_num) (by norm_num) R041 (h 1 one_ne_zero)
  obtain ⟨-, -, ⟨a, b⟩, -⟩ := FREta.eta_numbers
  rw [abs_le] at hc; subst this; norm_num at a b hc; linarith [hc.1, hc.2]

theorem blind_eta30Num250_false : ¬ FREtaBlind.Eta30Num250 := by
  rintro ⟨c, hc, h⟩
  have := coeff30 (by norm_num) (by norm_num) R250 (h 1 one_ne_zero)
  obtain ⟨-, -, -, ⟨a, b⟩⟩ := FREta.eta_numbers
  rw [abs_le] at hc; subst this; norm_num at a b hc; linarith [hc.1, hc.2]

/-- Sanity (our transcription): the printed closed forms reproduce the printed numbers
(0.152, −0.119, 4.02, −0.184), so the error is in the formulas (11.42)–(11.43). -/
theorem printed_numbers :
    FREta.printed20 (41 / 1000) ∈ Set.Ioo 0.15 0.155 ∧ FREta.printed20 (1 / 4) ∈ Set.Ioo (-0.12) (-0.115) ∧
    FREta.printed30 (41 / 1000) ∈ Set.Ioo 4 4.05 ∧ FREta.printed30 (1 / 4) ∈ Set.Ioo (-0.185) (-0.18) := by
  unfold FREta.printed20 FREta.printed30 FREta.printedDen
  norm_num [Set.mem_Ioo]

end Work.Cosmography.FREtaAudit
