import Mathlib

namespace ReaderB

open MeasureTheory Filter

/-- `T^n` for an integer `n`, as a map (inverse powers via the inverse equivalence). -/
def tpow {Ω : Type*} [MeasurableSpace Ω] (T : Ω ≃ᵐ Ω) (n : ℤ) : Ω → Ω :=
  ⇑(T.toEquiv ^ n)

/-- Mixing: μ(A ∩ T^{-n} B) → μ(A) μ(B) as |n| → ∞ (cofinite filter on ℤ). -/
def IsMixing {Ω : Type*} [MeasurableSpace Ω] (T : Ω ≃ᵐ Ω) (μ : Measure Ω) : Prop :=
  ∀ A B : Set Ω, MeasurableSet A → MeasurableSet B →
    Tendsto (fun n : ℤ => (μ (A ∩ tpow T n ⁻¹' B)).toReal) cofinite
      (nhds ((μ A).toReal * (μ B).toReal))

/-- Mixing of order k: for t strictly increasing integers whose consecutive gaps are all ≥ N, with N large. -/
def IsMixingOfOrder {Ω : Type*} [MeasurableSpace Ω] (T : Ω ≃ᵐ Ω) (μ : Measure Ω) (k : ℕ) : Prop :=
  ∀ A : Fin k → Set Ω, (∀ i, MeasurableSet (A i)) → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
    ∀ t : Fin k → ℤ, StrictMono t →
      (∀ i j : Fin k, i.val + 1 = j.val → (N : ℤ) ≤ t j - t i) →
      |(μ (⋂ i, tpow T (t i) ⁻¹' A i)).toReal - ∏ i, (μ (A i)).toReal| < ε

/-- Theorem 1.1, explicit form. -/
theorem reading_thm_1_1_explicit {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    (hmix : IsMixing T μ) :
    ∀ k : ℕ, 3 ≤ k → ∀ A : Fin k → Set Ω, (∀ i, MeasurableSet (A i)) →
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : Fin (k - 1) → ℕ, (∀ i, 0 < n i) → (∀ i, N ≤ n i) →
        |(μ (⋂ j : Fin k,
            tpow T ((∑ i : Fin (k - 1) with i.val < j.val, n i : ℕ) : ℤ) ⁻¹' A j)).toReal
          - ∏ j, (μ (A j)).toReal| < ε := sorry

/-- Definition-level form: mixing implies mixing of every order k ≥ 2. -/
theorem reading_thm_1_1_mixing_of_every_order {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    (hmix : IsMixing T μ) :
    ∀ k : ℕ, 2 ≤ k → IsMixingOfOrder T μ k := sorry

/-
Ambiguities / choices
- Invertible + measurable inverse: T : Ω ≃ᵐ Ω (MeasurableEquiv); measure-preserving: MeasurePreserving T μ μ.
  Probability space: [MeasurableSpace Ω], μ with [IsProbabilityMeasure μ]; no standardness assumed.
- T^{-n}B = preimage of B under T^n, T^n = (T.toEquiv ^ n) for n : ℤ (Equiv.Perm power); tpow.
- "|n| → ∞": `cofinite` on ℤ. Measures are converted with `.toReal` (finite for a probability measure, so no
  ⊤ junk); the limit is stated as Tendsto in ℝ.
- Mixing of order k: limit statement written as ε-N: ∀ε ∃N, for all strictly increasing integer t_1<…<t_k with
  every consecutive gap ≥ N, |μ(⋂ T^{-t_i}A_i) − ∏ μ(A_i)| < ε. This is "min gap → ∞" with A_i fixed.
  Indexing is Fin k, so the gap condition is over i, j with j = i+1 (no ℕ subtraction there).
- Explicit form: n : Fin (k-1) → ℕ positive integers, min n_i ≥ N; shift of A_j is the sum of n_i with i < j
  (0-indexed, so A_0 has shift 0, A_{j} has n_0+…+n_{j-1}). `k - 1` is ℕ subtraction but k ≥ 3 is a
  hypothesis, so it is truthful, not junk. Shift cast ℕ → ℤ.
- Sets A_i measurable (as ℱ-sets); μ is on all sets as an outer measure but only measurable ones are used.
- Hypothesis hT is listed per the source; the explicit form needs only mixing for k ≥ 3 plus preservation.
- Mixing hypothesis uses A,B in the sigma algebra, as in the source.
-/

end ReaderB
