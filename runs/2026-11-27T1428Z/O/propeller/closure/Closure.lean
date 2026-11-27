import Mathlib
import Readings.propeller
import ComparatorChallenges.GaussianPropeller

/-! # Target O, family O50 (Gaussian propeller): closures (run 2026-11-27T1428Z).
Frozen statement `all_partitions` (Gaussian measure `stdGaussian`, partitions up to null sets), taken by name,
never retyped. All three readers wrote the Gaussian as Lebesgue measure with density `(2π)^{-d/2} e^{-‖x‖²/2}`;
Mathlib had no theorem linking that density to `stdGaussian`. It is proved here (`stdGaussian_eq_withDensity`, by
characteristic functions: Mathlib's Gaussian Fourier integral on inner product spaces), a general tool for any
outside result stated with Mathlib's Gaussian. Closed from the frozen statement: every reader's inequality
(3/3), including reader A's integrability conjunct and reader C's partitions up to null sets. The sharpness
sentence is not closed: the readers' sectors (through `Complex.arg`) and the frozen sectors (through `√3`
inequalities) differ on boundary rays, and their equality up to null sets is not written. -/

namespace TargetO.Propeller

open MeasureTheory ProbabilityTheory Complex GaussianFourier OAI.GaussianPropeller
open scoped InnerProductSpace ENNReal NNReal Real

variable {d : ℕ}


variable {d : ℕ}

/-- The standard Gaussian density on `ℝ^d`. -/
noncomputable def gdens (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (2 * π) ^ (-(d : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / 2)

theorem gdens_nonneg (x : EuclideanSpace ℝ (Fin d)) : 0 ≤ gdens d x := by
  unfold gdens; positivity

theorem integrable_gdens : Integrable (gdens d) := by
  have h := integrable_cexp_neg_mul_sq_norm_add (V := EuclideanSpace ℝ (Fin d))
    (show 0 < ((1 / 2 : ℝ) : ℂ).re by simp) 0 0
  have h2 : Integrable (fun v : EuclideanSpace ℝ (Fin d) => Real.exp (-(1 / 2) * ‖v‖ ^ 2)) := by
    refine h.norm.congr (Filter.Eventually.of_forall fun v => ?_)
    simp only [zero_mul, add_zero, Complex.norm_exp]
    congr 1
    simp [← ofReal_pow]
  refine (h2.const_mul ((2 * π) ^ (-(d : ℝ) / 2))).congr (Filter.Eventually.of_forall fun v => ?_)
  simp only [gdens]; congr 2; ring

theorem charFun_gdens (t : EuclideanSpace ℝ (Fin d)) :
    charFun (volume.withDensity (fun x => ENNReal.ofReal (gdens d x))) t = cexp (-‖t‖ ^ 2 / 2) := by
  rw [charFun_apply]
  have hm : Measurable (fun x : EuclideanSpace ℝ (Fin d) => Real.toNNReal (gdens d x)) := by
    unfold gdens; fun_prop
  change ∫ x, cexp (⟪x, t⟫_ℝ * I) ∂(volume.withDensity (fun x => ((Real.toNNReal (gdens d x) : ℝ≥0) : ℝ≥0∞))) = _
  rw [integral_withDensity_eq_integral_smul hm]
  have e : ∀ x : EuclideanSpace ℝ (Fin d), Real.toNNReal (gdens d x) • cexp (⟪x, t⟫_ℝ * I) =
      ((2 * π) ^ (-(d : ℝ) / 2) : ℝ) * cexp (-((1 / 2 : ℝ) : ℂ) * ‖x‖ ^ 2 + I * ⟪t, x⟫_ℝ) := by
    intro x
    rw [NNReal.smul_def, Real.coe_toNNReal _ (gdens_nonneg x)]
    simp only [gdens, real_inner_comm x t]
    rw [Complex.real_smul, ofReal_mul, mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
    congr 2
    push_cast; ring
  simp_rw [e]
  rw [integral_const_mul, integral_cexp_neg_mul_sq_norm_add (show 0 < ((1 / 2 : ℝ) : ℂ).re by simp)]
  rw [finrank_euclideanSpace, Fintype.card_fin]
  have h2 : (π : ℂ) / ((1 / 2 : ℝ) : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; field_simp
  rw [h2, ← mul_assoc]
  have h3 : (((2 * π) ^ (-(d : ℝ) / 2) : ℝ) : ℂ) * ((2 * π : ℝ) : ℂ) ^ ((d : ℂ) / 2) = 1 := by
    rw [show ((d : ℂ) / 2) = (((d : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring]
    rw [← ofReal_cpow (by positivity), ← ofReal_mul, ← Real.rpow_add (by positivity), neg_div,
      neg_add_cancel, Real.rpow_zero, ofReal_one]
  rw [h3, one_mul]
  congr 1
  simp only [I_sq]; push_cast; field_simp; ring

/-- Mathlib's standard Gaussian on `ℝ^d` has the density `(2π)^{-d/2} e^{-‖x‖²/2}`. -/
theorem stdGaussian_eq_withDensity :
    stdGaussian (EuclideanSpace ℝ (Fin d)) = volume.withDensity (fun x => ENNReal.ofReal (gdens d x)) := by
  have : IsFiniteMeasure (volume.withDensity (fun x => ENNReal.ofReal (gdens d x))) :=
    isFiniteMeasure_withDensity_ofReal integrable_gdens.2
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_gdens, charFun_stdGaussian]


theorem frozen_gaussian (d : ℕ) :
    gaussian d = volume.withDensity (fun x => ENNReal.ofReal (gdens d x)) := stdGaussian_eq_withDensity

theorem value_eq {k : ℕ} (A : Fin k → Set (Space d)) (μ : Measure (Space d)) (hμ : gaussian d = μ) :
    value A = ∑ i, ‖∫ x in A i, x ∂μ‖ ^ 2 := by
  unfold value centroid; rw [hμ]

theorem part_of_cover {k : ℕ} (A : Fin k → Set (Space d)) (hm : ∀ i, MeasurableSet (A i))
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) (hc : (⋃ i, A i) = Set.univ) : IsPartition A := by
  refine ⟨hm, Filter.Eventually.of_forall fun x => ?_⟩
  have hx : x ∈ ⋃ i, A i := hc ▸ Set.mem_univ x
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
  refine ⟨i, hi, fun j hj => ?_⟩
  by_contra hne
  exact Set.disjoint_left.1 (hd hne) hj hi

theorem A_bound (H : AllPartitions) : type_of% @ReaderA.readingPropellerBound := by
  intro d k hd hk A hA
  have hμ : gaussian d = ReaderA.gaussianMeasure d := frozen_gaussian d
  refine ⟨fun i => ?_, ?_⟩
  · have : Integrable (fun x : Space d => x) (gaussian d) := by
      unfold gaussian; exact IsGaussian.integrable_id
    rw [hμ] at this
    exact this.integrableOn
  · have := H.1 d k hd hk A (part_of_cover A hA.1 hA.2.1 hA.2.2)
    rw [value_eq A _ hμ] at this
    exact this

theorem B_bound (H : AllPartitions) : type_of% @ReaderB.reading_propeller_bound := by
  intro d k hd hk A hA
  have hμ : gaussian d = ReaderB.gaussian d := frozen_gaussian d
  have := H.1 d k hd hk A (part_of_cover A hA.1 hA.2.1 hA.2.2)
  rw [value_eq A _ hμ] at this
  exact this

theorem C_bound (H : AllPartitions) : type_of% @ReaderC.reading_propeller_ineq := by
  intro d k hd hk A hA
  have hμ : gaussian d = ReaderC.gaussMeasure d := frozen_gaussian d
  have hpart : IsPartition A := by
    refine ⟨hA.1, ?_⟩
    have h1 : ∀ᵐ x ∂(gaussian d), x ∈ ⋃ i, A i := by
      rw [hμ, ae_iff]; simpa [Set.compl_def] using hA.2.2
    have h2 : ∀ᵐ x ∂(gaussian d), ∀ i j, i ≠ j → x ∉ A i ∩ A j := by
      rw [hμ]
      simp only [ae_all_iff]
      intro i j hij
      rw [ae_iff]
      simpa using hA.2.1 i j hij
    filter_upwards [h1, h2] with x hx hx2
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    exact ⟨i, hi, fun j hj => by by_contra hne; exact hx2 j i hne ⟨hj, hi⟩⟩
  have := H.1 d k (by omega) (by omega) A hpart
  rw [value_eq A _ hμ] at this
  exact this

end TargetO.Propeller

#print axioms TargetO.Propeller.stdGaussian_eq_withDensity
#print axioms TargetO.Propeller.A_bound
#print axioms TargetO.Propeller.B_bound
#print axioms TargetO.Propeller.C_bound
