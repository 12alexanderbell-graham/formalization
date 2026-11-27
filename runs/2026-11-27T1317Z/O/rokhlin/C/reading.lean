import Mathlib

open MeasureTheory Filter Topology
open scoped ENNReal

namespace ReaderC

/-! Definitions written from the source text (abstract and Section 1).

Conventions:
* An invertible measurable transformation with measurable inverse is a `T : Equiv.Perm Ω`
  together with `Measurable ⇑T` and `Measurable ⇑T.symm`.
* T^n for n : ℤ is the zpow in `Equiv.Perm Ω`; T^{-n} B is the preimage of B under T^n,
  i.e. `(⇑(T ^ n)) ⁻¹' B`, which is the image of B under T^{-n}.
* Measures are `ℝ≥0∞`-valued. -/

/-- Shift for the j-th set in the explicit form: n_1 + … + n_{j-1} (with j indexed from 0,
so the first shift is 0). The sum is over the indices i with i < j. -/
def shift {p : ℕ} (n : Fin (p + 2) → ℕ) (j : Fin (p + 3)) : ℤ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin (p + 2) => i.val < j.val), (n i : ℤ)

/-- Two-set mixing: μ(A ∩ T^{-n}B) → μ(A)μ(B) as |n| → ∞. On ℤ, |n| → ∞ is the cofinite
filter. -/
def IsMixing {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (T : Equiv.Perm Ω) : Prop :=
  ∀ A B : Set Ω, MeasurableSet A → MeasurableSet B →
    Tendsto (fun n : ℤ => μ (A ∩ (⇑(T ^ n)) ⁻¹' B)) cofinite (𝓝 (μ A * μ B))

/-- Mixing of order k = p + 2 with the explicit definition: for integer tuples t : Fin (p+2) → ℤ,
along the filter of tuples that are strictly increasing with all consecutive gaps ≥ M for M → ∞
(i.e. min_{i<k}(t_{i+1} - t_i) → ∞), the measure of ⋂ T^{-t_i} A_i tends to ∏ μ(A_i).
The filter is ⨅ over M of principal filters, and M ranges over ℕ. -/
def MixingOfOrder {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (T : Equiv.Perm Ω)
    (p : ℕ) : Prop :=
  ∀ A : Fin (p + 2) → Set Ω, (∀ i, MeasurableSet (A i)) →
    Tendsto (fun t : Fin (p + 2) → ℤ => μ (⋂ i, (⇑(T ^ (t i)) ⁻¹' A i)))
      (⨅ M : ℕ, 𝓟 {t : Fin (p + 2) → ℤ |
        StrictMono t ∧ ∀ i : Fin (p + 1), (M : ℤ) ≤ t i.succ - t i.castSucc})
      (𝓝 (∏ i, μ (A i)))

/-! Readings of the claims. -/

/-- Theorem 1.1 in explicit form: for every k ≥ 3 (k = p + 3) and measurable A_1…A_k, the
displayed intersection has measure tending to ∏ μ(A_j) as min(n_1,…,n_{k-1}) → ∞ through
positive integers. The filter is ⨅ over M of principal filters of tuples with all entries
positive and ≥ M. -/
theorem reading_thm_1_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (T : Equiv.Perm Ω)
    (hT : Measurable ⇑T) (hTinv : Measurable ⇑T.symm)
    (hmp : MeasurePreserving ⇑T μ μ) (hmix : IsMixing μ T) :
    ∀ p : ℕ, ∀ A : Fin (p + 3) → Set Ω, (∀ j, MeasurableSet (A j)) →
      Tendsto (fun n : Fin (p + 2) → ℕ =>
          μ (⋂ j, (⇑(T ^ (shift n j)))⁻¹' A j))
        (⨅ M : ℕ, 𝓟 {n : Fin (p + 2) → ℕ | ∀ i, 0 < n i ∧ M ≤ n i})
        (𝓝 (∏ j, μ (A j))) := sorry

/-- Definition-level form as a second theorem: mixing of every order k = p + 2 ≥ 2. -/
theorem reading_mixing_every_order {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (T : Equiv.Perm Ω)
    (hT : Measurable ⇑T) (hTinv : Measurable ⇑T.symm)
    (hmp : MeasurePreserving ⇑T μ μ) (hmix : IsMixing μ T) :
    ∀ p : ℕ, MixingOfOrder μ T p := sorry

end ReaderC

/-
AMBIGUITIES AND CHOICES (reader C, family O43 rokhlin)

1. Transformation: "invertible, measurable, measurable inverse, probability-preserving" is encoded
   as T : Equiv.Perm Ω with Measurable ⇑T, Measurable ⇑T.symm, and MeasurePreserving ⇑T μ μ.
   Equiv.Perm is used instead of MeasurableEquiv so that integer powers T^n are available as
   zpow in a group. The text's standing assumptions are all present as hypotheses.
2. Powers and T^{-n}B: T^n for n : ℤ is (T ^ n) in Equiv.Perm Ω. T^{-n}B is the image of B under
   T^{-n}, which equals the preimage (⇑(T ^ n)) ⁻¹' B. I used the preimage form throughout.
3. Mixing (two-set): |n| → ∞ on ℤ is the cofinite filter; the limit is in ℝ≥0∞ (no toReal needed,
   since μ is a probability measure and products are finite). Measurability of A and B is required.
4. Mixing of order k: the condition "min_{i<k}(t_{i+1} - t_i) → ∞" is encoded as a filter on
   tuples t : Fin (p+2) → ℤ: the infimum over M : ℕ of principal filters on
   {strictly increasing t with all consecutive gaps ≥ M}. Tuples outside the strictly increasing
   set are in the domain but excluded by the filter. The index is k = p + 2 with p : ℕ, so k ≥ 2.
   The text's "invariance allows t_1 = 0" is not used.
5. Explicit Theorem 1.1: indexed by k = p + 3 (so k ≥ 3) with A : Fin (p+3) → Set Ω. The shifts are
   shift n j = Σ_{i < j} n_i with the sum over i : Fin (p+2) with i.val < j.val, so the first set has
   shift 0 and the j-th set has shift n_0 + … + n_{j-1}, matching T^{-(n_1+…+n_{j-1})}A_j in the
   1-indexed text. The filter is the infimum over M : ℕ of principal filters on tuples n with all
   entries in positive integers and ≥ M, which is "min(n_1,…,n_{k-1}) → ∞ through positive integers".
   Shifts are ℤ-valued, so no ℕ subtraction arises.
6. Limit in Theorem 1.1 is toward ∏ μ(A_j) in ℝ≥0∞, consistent with probability measures.
7. The "no standardness" remark is a statement about the hypotheses (none are added), so nothing
   extra is encoded. The corollary on endomorphisms and flows is outside the requested readings.
-/
