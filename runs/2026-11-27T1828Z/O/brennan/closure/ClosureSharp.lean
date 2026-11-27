import Readings.brennan
import ComparatorChallenges.BrennanSharp

/-!
# Target O, family O64 (Brennan paper, Corollary on the Koebe function): closure of readings A, B, C

Against OpenAI's frozen `OAI.Brennan.Sharp.sharp_endpoints : SharpEndpointStatement` (used only
through `type_of%`):

* Reader B's corollary is the frozen first three conjuncts verbatim (the readers' Koebe function and
  class unfold to the frozen ones; `areaMoment` is the lower integral of the real power).
* Reader C's corollary states non-integrability of the two disk powers: for a measurable derivative,
  non-integrability of a nonnegative real power is the divergence of the lower integral of its
  `ofReal`, so it is equivalent, conjunct by conjunct, to the frozen first three conjuncts.
* Reader A's corollary uses the lower integral of the `NNReal` norm power. That power dominates the
  `ofReal` of the real power everywhere, so the frozen divergences imply reader A's; conversely the
  Koebe derivative vanishes almost nowhere on the disk (an injective holomorphic map), so with the
  membership conjunct the two are equivalent.
* Reader A's inverse sentence quantifies over every left inverse of the Koebe map on the disk. Any such
  map agrees with the frozen `koebeInverse` on the Koebe domain, which is open (open mapping theorem),
  so their derivatives agree there and the frozen non-integrability at the two domain endpoints gives
  reader A's divergences; conversely, applied to `koebeInverse` itself, reader A's sentence gives the
  frozen last two conjuncts (given the membership conjunct).
* Readers B and C did not state the inverse sentence (a reader coverage gap, not a mismatch).
-/

namespace TargetO.BrennanSharp

open OAI.Brennan OAI.Brennan.Sharp MeasureTheory Filter Topology Set
open scoped ENNReal

theorem A_koebe_eq : ReaderA.koebe = koebeMap := rfl
theorem B_koebe_eq : ReaderB.koebe = koebeMap := rfl
theorem C_koebe_eq : ReaderC.koebe = koebeMap := rfl

theorem C_Schlicht_iff (f : ℂ → ℂ) : f ∈ ReaderC.schlicht ↔ Schlicht f :=
  ⟨fun ⟨a, b, c, d⟩ => ⟨⟨a, b⟩, c, d⟩, fun ⟨⟨a, b⟩, c, d⟩ => ⟨a, b, c, d⟩⟩

/-! ## Norm powers -/

theorem ofReal_rpow_norm_of_nonneg (x : ℂ) {s : ℝ} (hs : 0 ≤ s) :
    ENNReal.ofReal (‖x‖ ^ s) = (‖x‖₊ : ℝ≥0∞) ^ s := by
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hs, ← coe_nnnorm, ENNReal.ofReal_coe_nnreal]

theorem ofReal_rpow_norm_of_ne (x : ℂ) (hx : x ≠ 0) (s : ℝ) :
    ENNReal.ofReal (‖x‖ ^ s) = (‖x‖₊ : ℝ≥0∞) ^ s := by
  rw [← ENNReal.ofReal_rpow_of_pos (norm_pos_iff.2 hx), ← coe_nnnorm, ENNReal.ofReal_coe_nnreal]

/-- The `NNReal` norm power dominates the `ofReal` of the real norm power everywhere. -/
theorem ofReal_rpow_norm_le (x : ℂ) (s : ℝ) :
    ENNReal.ofReal (‖x‖ ^ s) ≤ (‖x‖₊ : ℝ≥0∞) ^ s := by
  by_cases hx : x = 0
  · subst hx
    by_cases hs : s = 0
    · subst hs; simp
    · rw [norm_zero, Real.zero_rpow hs, ENNReal.ofReal_zero]; exact zero_le
  · exact (ofReal_rpow_norm_of_ne x hx s).le

theorem integrableOn_iff_ofReal (g : ℂ → ℂ) (hg : Measurable g) (U : Set ℂ) (s : ℝ) :
    IntegrableOn (fun z => ‖g z‖ ^ s) U volume ↔
      ∫⁻ z in U, ENNReal.ofReal (‖g z‖ ^ s) < ∞ := by
  have hm : AEStronglyMeasurable (fun z => ‖g z‖ ^ s) (volume.restrict U) :=
    (hg.norm.pow_const s).aestronglyMeasurable
  have hnn : 0 ≤ᵐ[volume.restrict U] fun z => ‖g z‖ ^ s :=
    ae_of_all _ fun z => Real.rpow_nonneg (norm_nonneg _) _
  exact ⟨fun hi => (hasFiniteIntegral_iff_ofReal hnn).1 hi.2,
    fun hl => ⟨hm, (hasFiniteIntegral_iff_ofReal hnn).2 hl⟩⟩

theorem not_integrableOn_iff (g : ℂ → ℂ) (hg : Measurable g) (U : Set ℂ) (s : ℝ) :
    ¬ IntegrableOn (fun z => ‖g z‖ ^ s) U volume ↔
      ∫⁻ z in U, ENNReal.ofReal (‖g z‖ ^ s) = ⊤ := by
  rw [integrableOn_iff_ofReal g hg U s, not_lt_top_iff]

/-- The derivative of an injective holomorphic map on the disk vanishes almost nowhere there. -/
theorem ae_deriv_ne_zero {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f disk) (hinj : InjOn f disk) :
    ∀ᵐ z ∂(volume.restrict disk), deriv f z ≠ 0 := by
  have hopen : IsOpen disk := Metric.isOpen_ball
  have han : AnalyticOnNhd ℂ f disk := hf.analyticOnNhd hopen
  have hconn : IsConnected disk :=
    (convex_ball (0 : ℂ) 1).isConnected (Metric.nonempty_ball.2 one_pos)
  have h0 : (0 : ℂ) ∈ disk := Metric.mem_ball_self one_pos
  have h1 : ((1 / 2 : ℝ) : ℂ) ∈ disk := by
    show _ ∈ Metric.ball (0 : ℂ) 1
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; norm_num
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ disk, deriv f x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have := hopen.is_const_of_deriv_eq_zero hconn.isPreconnected hf (fun z hz => hcon z hz) h0 h1
    have h01 := hinj h0 h1 this
    have : ((1 / 2 : ℝ) : ℂ) ≠ 0 := by
      rw [Ne, Complex.ofReal_eq_zero]; norm_num
    exact this h01.symm
  have hcd := han.deriv.preimage_zero_mem_codiscreteWithin hx0 hx hconn
  exact ae_restrict_le_codiscreteWithin hopen.measurableSet hcd

theorem lintegral_ofReal_eq {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f disk) (hinj : InjOn f disk)
    (s : ℝ) : ∫⁻ z in disk, ENNReal.ofReal (‖deriv f z‖ ^ s) =
      ∫⁻ z in disk, (‖deriv f z‖₊ : ℝ≥0∞) ^ s := by
  refine lintegral_congr_ae ?_
  filter_upwards [ae_deriv_ne_zero hf hinj] with z hz using ofReal_rpow_norm_of_ne _ hz s

/-! ## The Koebe domain and left inverses -/

theorem koebeDomain_isOpen (h : Schlicht koebeMap) : IsOpen koebeDomain := by
  have han : AnalyticOnNhd ℂ koebeMap disk := h.1.1.analyticOnNhd Metric.isOpen_ball
  rcases han.is_constant_or_isOpen (convex_ball (0 : ℂ) 1).isPreconnected with ⟨w, hw⟩ | hopen
  · exfalso
    have h0 : (0 : ℂ) ∈ disk := Metric.mem_ball_self one_pos
    have h1 : ((1 / 2 : ℝ) : ℂ) ∈ disk := by
      show _ ∈ Metric.ball (0 : ℂ) 1
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; norm_num
    have h01 := h.1.2 h0 h1 ((hw 0 h0).trans (hw _ h1).symm)
    have : ((1 / 2 : ℝ) : ℂ) ≠ 0 := by
      rw [Ne, Complex.ofReal_eq_zero]; norm_num
    exact this h01.symm
  · exact hopen disk subset_rfl Metric.isOpen_ball

theorem eqOn_koebeInverse (h : Schlicht koebeMap) {φ : ℂ → ℂ}
    (hφ : ∀ z ∈ disk, φ (koebeMap z) = z) : EqOn φ koebeInverse koebeDomain := by
  rintro _ ⟨z, hz, rfl⟩
  have hex : ∃ a ∈ disk, koebeMap a = koebeMap z := ⟨z, hz, rfl⟩
  rw [hφ z hz]
  exact (h.1.2 (Function.invFunOn_mem hex) hz (Function.invFunOn_eq hex)).symm

theorem deriv_eqOn_koebeInverse (h : Schlicht koebeMap) {φ : ℂ → ℂ}
    (hφ : ∀ z ∈ disk, φ (koebeMap z) = z) :
    EqOn (deriv φ) (deriv koebeInverse) koebeDomain := fun _ hw =>
  (eventuallyEq_of_mem ((koebeDomain_isOpen h).mem_nhds hw) (eqOn_koebeInverse h hφ)).deriv_eq

/-- Divergence for every left inverse, from non-integrability of `koebeInverse`'s power. -/
theorem lintegral_left_inverse_eq_top (h : Schlicht koebeMap) {φ : ℂ → ℂ}
    (hφ : ∀ z ∈ disk, φ (koebeMap z) = z) {s : ℝ} (hs : 0 ≤ s)
    (hni : ¬ IntegrableOn (fun z => ‖deriv koebeInverse z‖ ^ s) koebeDomain volume) :
    ∫⁻ z in koebeDomain, (‖deriv φ z‖₊ : ℝ≥0∞) ^ s = ⊤ := by
  rw [not_integrableOn_iff _ (measurable_deriv _)] at hni
  rw [← hni]
  refine setLIntegral_congr_fun (koebeDomain_isOpen h).measurableSet fun z hz => ?_
  rw [deriv_eqOn_koebeInverse h hφ hz, ofReal_rpow_norm_of_nonneg _ hs]

theorem koebeInverse_left_inverse (h : Schlicht koebeMap) :
    ∀ z ∈ disk, koebeInverse (koebeMap z) = z := fun z hz =>
  have hex : ∃ a ∈ disk, koebeMap a = koebeMap z := ⟨z, hz, rfl⟩
  h.1.2 (Function.invFunOn_mem hex) hz (Function.invFunOn_eq hex)

/-! ## Closures -/

/-- Reader A: both corollary theorems follow from the frozen statement. -/
theorem closure_A (h : type_of% @OAI.Brennan.Sharp.sharp_endpoints) :
    (type_of% @ReaderA.reading_cor_1_2_koebe) ∧ (type_of% @ReaderA.reading_cor_1_2_inverse) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨⟨h1, ?_, ?_⟩, fun φ hφ => ⟨?_, ?_⟩⟩
  · exact eq_top_mono (lintegral_mono fun _ => ofReal_rpow_norm_le _ _) h2
  · exact eq_top_mono (lintegral_mono fun _ => ofReal_rpow_norm_le _ _) h3
  · exact lintegral_left_inverse_eq_top h1 hφ (by norm_num) h4
  · exact lintegral_left_inverse_eq_top h1 hφ (by norm_num) h5

/-- Reader A's Koebe theorem gives back the frozen first three conjuncts. -/
theorem closure_A_koebe_converse (hA : type_of% @ReaderA.reading_cor_1_2_koebe) :
    Schlicht koebeMap ∧ areaMoment koebeMap disk (-2) = ⊤ ∧
      areaMoment koebeMap disk (2 / 3) = ⊤ := by
  obtain ⟨h1, h2, h3⟩ := hA
  have h1' : Schlicht koebeMap := h1
  refine ⟨h1', ?_, ?_⟩
  · unfold areaMoment; rw [lintegral_ofReal_eq h1'.1.1 h1'.1.2]; exact h2
  · unfold areaMoment; rw [lintegral_ofReal_eq h1'.1.1 h1'.1.2]; exact h3

/-- Reader A's inverse sentence, with the membership conjunct, gives back the frozen last two
conjuncts (apply it to `koebeInverse`). -/
theorem closure_A_inverse_converse (h1 : Schlicht koebeMap)
    (hA : type_of% @ReaderA.reading_cor_1_2_inverse) :
    ¬ IntegrableOn (fun z => ‖deriv koebeInverse z‖ ^ (4 : ℝ)) koebeDomain volume ∧
      ¬ IntegrableOn (fun z => ‖deriv koebeInverse z‖ ^ (4 / 3 : ℝ)) koebeDomain volume := by
  obtain ⟨h4, h43⟩ := hA koebeInverse (koebeInverse_left_inverse h1)
  constructor
  · rw [not_integrableOn_iff _ (measurable_deriv _), ← h4]
    refine setLIntegral_congr_fun (koebeDomain_isOpen h1).measurableSet fun z _ => ?_
    exact ofReal_rpow_norm_of_nonneg _ (by norm_num)
  · rw [not_integrableOn_iff _ (measurable_deriv _), ← h43]
    refine setLIntegral_congr_fun (koebeDomain_isOpen h1).measurableSet fun z _ => ?_
    exact ofReal_rpow_norm_of_nonneg _ (by norm_num)

/-- Reader B: the corollary follows from the frozen statement ... -/
theorem closure_B (h : type_of% @OAI.Brennan.Sharp.sharp_endpoints) :
    type_of% @ReaderB.readingKoebe :=
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- ... and is literally the frozen first three conjuncts. -/
theorem closure_B_converse (hB : type_of% @ReaderB.readingKoebe) :
    Schlicht koebeMap ∧ areaMoment koebeMap disk (-2) = ⊤ ∧
      areaMoment koebeMap disk (2 / 3) = ⊤ := hB

/-- Reader C: the corollary follows from the frozen statement ... -/
theorem closure_C (h : type_of% @OAI.Brennan.Sharp.sharp_endpoints) :
    type_of% @ReaderC.reading_cor_1_2 := by
  obtain ⟨h1, h2, h3, -, -⟩ := h
  refine ⟨(C_Schlicht_iff _).2 h1, ?_, ?_⟩
  · exact (not_integrableOn_iff _ (measurable_deriv _) _ _).2 h2
  · exact (not_integrableOn_iff _ (measurable_deriv _) _ _).2 h3

/-- ... and gives back the frozen first three conjuncts. -/
theorem closure_C_converse (hC : type_of% @ReaderC.reading_cor_1_2) :
    Schlicht koebeMap ∧ areaMoment koebeMap disk (-2) = ⊤ ∧
      areaMoment koebeMap disk (2 / 3) = ⊤ := by
  obtain ⟨h1, h2, h3⟩ := hC
  exact ⟨(C_Schlicht_iff _).1 h1, (not_integrableOn_iff _ (measurable_deriv _) _ _).1 h2,
    (not_integrableOn_iff _ (measurable_deriv _) _ _).1 h3⟩

end TargetO.BrennanSharp

#print axioms TargetO.BrennanSharp.closure_A
#print axioms TargetO.BrennanSharp.closure_A_koebe_converse
#print axioms TargetO.BrennanSharp.closure_A_inverse_converse
#print axioms TargetO.BrennanSharp.closure_B
#print axioms TargetO.BrennanSharp.closure_B_converse
#print axioms TargetO.BrennanSharp.closure_C
#print axioms TargetO.BrennanSharp.closure_C_converse
