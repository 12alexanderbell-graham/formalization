import Mathlib
import Readings.Anderson
import ComparatorChallenges.PlanarAndersonSpectrum

/-! # Target O, family O39 (planar Anderson): closures (run 2026-11-27T1317Z).
Frozen statement (`anderson_spectrum_ae`: a.s. a bounded self-adjoint H_v exists, with spectrum [−4−h, 4+h]) taken
with `type_of%`, never retyped. Closed: every reader's conclusion (i), the spectrum. The three readers model the
randomness differently (A, B: any probability space with independent coordinates of the uniform law; C: a law on
configurations with independent coordinates); each is transported to the frozen `disorderLaw` by
`iIndepFun.map_fun_eq_infinitePi_map₀`. B and C quantify over every operator with the H_v formula: an operator on
ℓ² is determined by the formula, so it is the frozen one. Not closed, and not stated in the Lean: (ii) pure-point
type, (iii) eigenbasis, (iv) dense eigenvalues — OpenAI's scope document says the pure-point type is not asserted. -/

namespace TargetO.Anderson

open MeasureTheory ProbabilityTheory OAI.PlanarAnderson

/-- The uniform laws written by the readers are the frozen one. -/
theorem unif_eq (h : ℝ) (_hh : 0 < h) :
    (ENNReal.ofReal (2 * h))⁻¹ • volume.restrict (Set.Icc (-h) h) =
      ProbabilityTheory.cond (volume : Measure ℝ) (Set.Icc (-h) h) := by
  rw [ProbabilityTheory.cond, Real.volume_Icc]
  congr 3
  ring

theorem interval_eq (h : ℝ) :
    spectralInterval h = ((↑) : ℝ → ℂ) '' Set.Icc (-4 - h) (4 + h) := by
  ext z
  simp only [spectralInterval, Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨him, h1, h2⟩
    exact ⟨z.re, ⟨h1, h2⟩, Complex.ext (by simp) (by simp [him])⟩
  · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
    exact ⟨Complex.ofReal_im t, by rw [Complex.ofReal_re]; exact h1, by rw [Complex.ofReal_re]; exact h2⟩

/-- Under the frozen law, almost surely every site potential lies in [−h, h]. -/
theorem prob_inst (h : ℝ) (hh : 0 < h) :
    IsProbabilityMeasure (ProbabilityTheory.cond (volume : Measure ℝ) (Set.Icc (-h) h)) :=
  cond_isProbabilityMeasure_of_finite (by rw [Real.volume_Icc]; simp; linarith)
    (by rw [Real.volume_Icc]; simp)

theorem ae_bounded (h : ℝ) (hh : 0 < h) :
    ∀ᵐ v ∂disorderLaw h, ∀ x, |v x| ≤ h := by
  have := prob_inst h hh
  rw [ae_all_iff]
  intro x
  have hx : ∀ᵐ t ∂(disorderLaw h).map (fun v : Configuration => v x), t ∈ Set.Icc (-h) h := by
    rw [disorderLaw, Measure.infinitePi_map_eval]
    exact ae_cond_mem measurableSet_Icc
  filter_upwards [ae_of_ae_map (measurable_pi_apply x).aemeasurable hx] with v hv
  exact abs_le.2 hv

/-- Any two operators with the H_v formula coincide. -/
theorem op_unique (v : Configuration) (H H' : Hilbert →L[ℂ] Hilbert)
    (hH : IsAndersonOperator v H) (hH' : ∀ (u : Hilbert) (x : Site),
      (H' u) x = u (x.1 + 1, x.2) + u (x.1 - 1, x.2) + u (x.1, x.2 + 1) + u (x.1, x.2 - 1) +
        (v x : ℂ) * u x) : H = H' := by
  ext u x
  rw [hH u x, hH' u x]

/-- The transported frozen statement on an abstract probability space. -/
theorem frozen_on {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H0 : type_of% @anderson_spectrum_ae) (h : ℝ) (hh : 0 < h) (v : Site → Ω → ℝ)
    (hm : ∀ x, Measurable (v x)) (hi : iIndepFun v P)
    (hl : ∀ x, P.map (v x) = ProbabilityTheory.cond volume (Set.Icc (-h) h)) :
    ∀ᵐ ω ∂P, (∀ x, |v x ω| ≤ h) ∧ ∃ H : Hilbert →L[ℂ] Hilbert,
      IsAndersonOperator (fun x => v x ω) H ∧ IsSelfAdjoint H ∧
        spectrum ℂ H = spectralInterval h := by
  have hmeas : Measurable (fun ω x => v x ω) := measurable_pi_iff.2 hm
  have := prob_inst h hh
  have hlaw : P.map (fun ω x => v x ω) = disorderLaw h := by
    rw [hi.map_fun_eq_infinitePi_map₀ hmeas.aemeasurable, disorderLaw]
    congr 1
    funext x
    exact hl x
  have hb := ae_bounded h hh
  have hf := H0 hh
  rw [← hlaw] at hb hf
  filter_upwards [ae_of_ae_map hmeas.aemeasurable hb, ae_of_ae_map hmeas.aemeasurable hf]
    with ω h1 h2
  exact ⟨h1, h2⟩

theorem A_spectrum (H0 : type_of% @anderson_spectrum_ae) :
    type_of% @ReaderA.reading_thm_1_1_spectrum := by
  intro Ω _ P _ h hh v hv
  filter_upwards [frozen_on P H0 h hh v hv.meas hv.indep hv.unif] with ω ⟨_, H, hA, _, hs⟩
  refine ⟨H, fun u x => ?_, ?_⟩
  · rw [hA u x]
    simp only [ReaderA.nbrs]
    rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
    · ring
    all_goals simp [Prod.ext_iff]; try omega
  · rw [hs, interval_eq]
    rfl

theorem B_spectrum (H0 : type_of% @anderson_spectrum_ae) :
    type_of% @ReaderB.readingSpectrum := by
  intro Ω _ P _ h hh v hv
  have hl : ∀ x, P.map (v x) = ProbabilityTheory.cond volume (Set.Icc (-h) h) := fun x => by
    rw [hv.law x, ReaderB.unif, unif_eq h hh]
  filter_upwards [frozen_on P H0 h hh v hv.meas hv.indep hl] with ω ⟨_, H', hA, _, hs⟩
  intro H hB
  have : H' = H := op_unique _ H' H hA (fun u x => by
    rw [hB u x]
    simp only [ReaderB.nbrs]
    rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
    · have e1 : x + ((1 : ℤ), (0 : ℤ)) = (x.1 + 1, x.2) := Prod.ext (by simp) (by simp)
      have e2 : x + ((-1 : ℤ), (0 : ℤ)) = (x.1 - 1, x.2) := Prod.ext (by simp [sub_eq_add_neg]) (by simp)
      have e3 : x + ((0 : ℤ), (1 : ℤ)) = (x.1, x.2 + 1) := Prod.ext (by simp) (by simp)
      have e4 : x + ((0 : ℤ), (-1 : ℤ)) = (x.1, x.2 - 1) := Prod.ext (by simp) (by simp [sub_eq_add_neg])
      rw [e1, e2, e3, e4]
      ring
    all_goals decide)
  rw [← this, hs, interval_eq]

theorem C_spectrum (H0 : type_of% @anderson_spectrum_ae) :
    type_of% @ReaderC.reading_anderson_i := by
  intro H hH h hh P hP
  obtain ⟨hprob, hl, hi⟩ := hP
  have hl' : ∀ x, P.map (fun ω : Site → ℝ => ω x) =
      ProbabilityTheory.cond volume (Set.Icc (-h) h) := fun x => by
    rw [hl x, ReaderC.unifLaw, unif_eq h hh]
  filter_upwards [frozen_on P H0 h hh (fun x ω => ω x) (fun x => measurable_pi_apply x) hi hl']
    with ω ⟨hbd, H', hA, _, hs⟩
  have : H' = H ω := op_unique _ H' (H ω) hA (fun u x => by
    rw [hH h ω hbd u x, ReaderC.adjSum])
  rw [← this, hs, interval_eq]

end TargetO.Anderson

#print axioms TargetO.Anderson.A_spectrum
#print axioms TargetO.Anderson.B_spectrum
#print axioms TargetO.Anderson.C_spectrum
