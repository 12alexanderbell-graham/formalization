import Readings.strict
import ComparatorChallenges.StrictMeans

/-!
# Target O, family O64 (strict inverse-first-power paper): closure of readings A, B, C

Each reader's main theorem is proved equivalent, conjunct by conjunct, to OpenAI's frozen
`OAI.StrictInverseFirstPower.main` (used only through `type_of%`, never retyped):

* the uniform bound for the inverse-first-power mean: the readers' means equal the frozen
  `integralMean` (reciprocal written as `one_div`); reader B's extra `0 < C` is harmless (enlarge `C`);
  reader C's exponent is written with a negated numerator, equal to the frozen one;
* the consequence at exponent minus one: the readers' bounded classes coincide with
  `BoundedNormalizedUnivalent` (bounded image iff a norm bound on the disk), their suprema (`iSup` over
  membership, over a subtype, or `sSup` of an image) equal `boundedSpectrum`, and the frozen quarter,
  an `EReal` quotient, is the cast of the real quarter;
* the failure of Kraetzer's identity: the readers' real formula cast to `EReal` is `kraetzerPrediction`.

Reader A's unfolded form of the consequence (a real bound strictly below the quarter for every
exponent of a bounded map) is implied by the frozen statement, and implies reader A's own consequence
conjunct (hence the frozen one).
-/

namespace TargetO.BrennanStrict

open OAI.StrictInverseFirstPower Filter Topology

/-! ## Classes -/

theorem bounded_iff (f : ℂ → ℂ) :
    Bornology.IsBounded (f '' Metric.ball (0 : ℂ) 1) ↔
      ∃ R : ℝ, ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖f z‖ ≤ R := by
  rw [isBounded_iff_forall_norm_le]
  constructor
  · rintro ⟨R, hR⟩; exact ⟨R, fun z hz => hR _ ⟨z, hz, rfl⟩⟩
  · rintro ⟨R, hR⟩; exact ⟨R, by rintro _ ⟨z, hz, rfl⟩; exact hR z hz⟩

theorem A_SSS_iff (f : ℂ → ℂ) : f ∈ ReaderA.SSS ↔ NormalizedUnivalent f := Iff.rfl

theorem C_SSS_iff (f : ℂ → ℂ) : f ∈ ReaderC.SSS ↔ NormalizedUnivalent f := Iff.rfl

theorem B_SSS_iff (f : ℂ → ℂ) : ReaderB.IsSchlicht f ↔ NormalizedUnivalent f := Iff.rfl

theorem A_SSSb_iff (f : ℂ → ℂ) : f ∈ ReaderA.SSSb ↔ BoundedNormalizedUnivalent f :=
  and_congr Iff.rfl (bounded_iff f)

theorem C_SSSb_iff (f : ℂ → ℂ) : f ∈ ReaderC.SSSb ↔ BoundedNormalizedUnivalent f :=
  and_congr Iff.rfl (bounded_iff f)

theorem B_SSSb_iff (f : ℂ → ℂ) : ReaderB.IsSchlichtBounded f ↔ BoundedNormalizedUnivalent f :=
  Iff.rfl

/-! ## Means, exponents, spectra -/

theorem A_M_eq : ReaderA.M = integralMean := by
  funext p f r; simp only [ReaderA.M, integralMean, one_div]

theorem B_M_eq : ReaderB.intMean = integralMean := by
  funext p f r; simp only [ReaderB.intMean, integralMean, one_div]

theorem C_M_eq : ReaderC.Mp = integralMean := rfl

theorem A_beta_eq (f : ℂ → ℂ) (p : ℝ) : ReaderA.beta f p = growthExponent p f := by
  simp only [ReaderA.beta, growthExponent, A_M_eq]

theorem B_beta_eq (f : ℂ → ℂ) (p : ℝ) : ReaderB.beta f p = growthExponent p f := by
  simp only [ReaderB.beta, growthExponent, B_M_eq]

theorem C_beta_eq (p : ℝ) (f : ℂ → ℂ) : ReaderC.betaF p f = growthExponent p f := rfl

theorem A_Bb_eq : ReaderA.Bb = boundedSpectrum := by
  funext p
  unfold ReaderA.Bb boundedSpectrum
  refine iSup_congr fun f => iSup_congr_Prop (A_SSSb_iff f) fun _ => A_beta_eq f p

theorem B_Bb_eq : ReaderB.Bb = boundedSpectrum := by
  funext p
  unfold ReaderB.Bb boundedSpectrum
  rw [iSup_subtype]
  exact iSup_congr fun f => iSup_congr_Prop (B_SSSb_iff f) fun _ => B_beta_eq f p

theorem C_Bb_eq : ReaderC.Bb = boundedSpectrum := by
  funext p
  unfold ReaderC.Bb boundedSpectrum
  rw [sSup_image]
  exact iSup_congr fun f => iSup_congr_Prop (C_SSSb_iff f) fun _ => C_beta_eq p f

theorem A_kraetzer_eq (p : ℝ) : ((ReaderA.kraetzer p : ℝ) : EReal) = kraetzerPrediction p := by
  unfold ReaderA.kraetzer kraetzerPrediction; split_ifs <;> rfl

theorem B_kraetzer_eq (p : ℝ) : ((ReaderB.kraetzer p : ℝ) : EReal) = kraetzerPrediction p := by
  unfold ReaderB.kraetzer kraetzerPrediction; split_ifs <;> rfl

theorem C_kraetzer_eq (p : ℝ) : ((ReaderC.kraetzer p : ℝ) : EReal) = kraetzerPrediction p := by
  unfold ReaderC.kraetzer kraetzerPrediction; split_ifs <;> rfl

/-- The frozen quarter is an `EReal` quotient; it is the cast of the real quarter. -/
theorem quarter_eq : (1 / 4 : EReal) = ((1 / 4 : ℝ) : EReal) := by
  rw [EReal.coe_div]
  rfl

/-! ## Closures -/

/-- Reader A, main theorem: equivalent to the frozen statement, conjunct by conjunct. -/
theorem closure_A :
    type_of% @OAI.StrictInverseFirstPower.main ↔ type_of% @ReaderA.reading_theorem_1_1 := by
  rw [A_M_eq, A_Bb_eq, ← quarter_eq]
  simp only [A_kraetzer_eq]
  exact Iff.rfl

/-- Reader A's unfolded consequence follows from the frozen statement. -/
theorem closure_A_unfolded (h : type_of% @OAI.StrictInverseFirstPower.main) :
    type_of% @ReaderA.reading_Bb_lt_unfolded := by
  have h2 : ReaderA.Bb (-1) < ((1 / 4 : ℝ) : EReal) := by
    rw [A_Bb_eq, ← quarter_eq]; exact h.2.1
  obtain ⟨c, hBc, hc⟩ := EReal.lt_iff_exists_real_btwn.1 h2
  refine ⟨c, EReal.coe_lt_coe_iff.1 hc, fun f hf => le_trans ?_ hBc.le⟩
  exact le_iSup₂ (f := fun f (_ : f ∈ ReaderA.SSSb) => ReaderA.beta f (-1)) f hf

/-- Conversely, reader A's unfolded consequence gives reader A's (and so the frozen) consequence
conjunct. -/
theorem closure_A_unfolded_converse (h : type_of% @ReaderA.reading_Bb_lt_unfolded) :
    ReaderA.Bb (-1) < ((1 / 4 : ℝ) : EReal) := by
  obtain ⟨c, hc, hf⟩ := h
  exact lt_of_le_of_lt (iSup₂_le hf) (EReal.coe_lt_coe_iff.2 hc)

/-- Reader B, main theorem: equivalent to the frozen statement, conjunct by conjunct
(the extra `0 < C` is absorbed by replacing `C` with `max C 1`). -/
theorem closure_B :
    type_of% @OAI.StrictInverseFirstPower.main ↔ type_of% @ReaderB.readingStrictMain := by
  rw [B_M_eq, B_Bb_eq, ← quarter_eq]
  simp only [B_kraetzer_eq]
  refine and_congr ?_ Iff.rfl
  constructor
  · rintro ⟨ε, C, hε, hε4, hb⟩
    refine ⟨ε, max C 1, hε, hε4, lt_of_lt_of_le one_pos (le_max_right _ _),
      fun f hf r hr1 hr2 => (hb f hf r hr1 hr2).trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)
  · rintro ⟨ε, C, hε, hε4, -, hb⟩
    exact ⟨ε, C, hε, hε4, hb⟩

/-- Reader C, main theorem: equivalent to the frozen statement, conjunct by conjunct. -/
theorem closure_C :
    type_of% @OAI.StrictInverseFirstPower.main ↔ type_of% @ReaderC.reading_O64b_thm11 := by
  rw [C_M_eq, C_Bb_eq, ← quarter_eq, show (-1 / 4 : ℝ) = -(1 / 4) by norm_num]
  simp only [C_kraetzer_eq]
  exact Iff.rfl

end TargetO.BrennanStrict

#print axioms TargetO.BrennanStrict.closure_A
#print axioms TargetO.BrennanStrict.closure_A_unfolded
#print axioms TargetO.BrennanStrict.closure_A_unfolded_converse
#print axioms TargetO.BrennanStrict.closure_B
#print axioms TargetO.BrennanStrict.closure_C
