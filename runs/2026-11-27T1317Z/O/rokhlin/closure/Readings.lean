import Mathlib

namespace ReaderA

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The integer iterate `T^n` of an invertible transformation (a measurable equivalence). -/
def tIter (T : Ω ≃ᵐ Ω) (n : ℤ) : Ω → Ω :=
  ⇑((T.toEquiv : Equiv.Perm Ω) ^ n)

/-- `T^{-n} A`, the preimage of `A` under `T^n`. -/
def tPre (T : Ω ≃ᵐ Ω) (n : ℤ) (A : Set Ω) : Set Ω :=
  tIter T n ⁻¹' A

/-- `T` is mixing: `μ(A ∩ T^{-n}B) → μ(A)μ(B)` as `|n| → ∞` (over `n ∈ ℤ`),
for all measurable `A, B`. -/
def IsMixing (μ : Measure Ω) (T : Ω ≃ᵐ Ω) : Prop :=
  ∀ A B : Set Ω, MeasurableSet A → MeasurableSet B →
    Tendsto (fun n : ℤ => μ (A ∩ tPre T n B)) (comap (fun n : ℤ => |n|) atTop)
      (𝓝 (μ A * μ B))

/-- Filter on tuples `t : Fin k → ℤ`: `t₁ < ⋯ < t_k` and `min_{i<k}(t_{i+1} - t_i) → ∞`. -/
def gapAtTop (k : ℕ) : Filter (Fin k → ℤ) :=
  ⨅ N : ℕ, 𝓟 {t | StrictMono t ∧ ∀ i j : Fin k, j.val = i.val + 1 → (N : ℤ) ≤ t j - t i}

/-- Mixing of order `k`: `μ(⋂ᵢ T^{-tᵢ}Aᵢ) → ∏ᵢ μ(Aᵢ)` along `gapAtTop k`,
for every fixed choice of measurable `A₁, …, A_k`. -/
def IsMixingOfOrder (μ : Measure Ω) (T : Ω ≃ᵐ Ω) (k : ℕ) : Prop :=
  ∀ A : Fin k → Set Ω, (∀ i, MeasurableSet (A i)) →
    Tendsto (fun t : Fin k → ℤ => μ (⋂ i, tPre T (t i) (A i))) (gapAtTop k)
      (𝓝 (∏ i, μ (A i)))

/-- Filter on `(n₁, …, n_j) : Fin j → ℕ`: all entries positive and `min nᵢ → ∞`. -/
def minAtTop (j : ℕ) : Filter (Fin j → ℕ) :=
  ⨅ N : ℕ, 𝓟 {n | (∀ i, 0 < n i) ∧ ∀ i, N ≤ n i}

/-- Exponent `n₁ + ⋯ + n_{i}` (zero-based: sum of `n l` for `l < i`) attached to `A_{i+1}`. -/
def partialSum {j : ℕ} (n : Fin j → ℕ) (i : Fin (j + 1)) : ℤ :=
  ∑ l : Fin j with l.val < i.val, (n l : ℤ)

/-- Sanity: the limit filters are proper (not `⊥`), so the conclusions are not vacuous. -/
theorem minAtTop_neBot (j : ℕ) : (minAtTop j).NeBot := by
  apply iInf_neBot_of_directed'
  · intro a b
    refine ⟨max a b, ?_, ?_⟩ <;>
    · simp only [ge_iff_le, principal_mono]
      intro n hn
      exact ⟨hn.1, fun i => le_trans (by omega) (hn.2 i)⟩
  · intro N
    rw [principal_neBot_iff]
    exact ⟨fun _ => N + 1, fun _ => Nat.succ_pos N, fun _ => Nat.le_succ N⟩

theorem gapAtTop_neBot (k : ℕ) : (gapAtTop k).NeBot := by
  apply iInf_neBot_of_directed'
  · intro a b
    refine ⟨max a b, ?_, ?_⟩ <;>
    · simp only [ge_iff_le, principal_mono]
      intro t ht
      exact ⟨ht.1, fun i j hij => le_trans (by push_cast; omega) (ht.2 i j hij)⟩
  · intro N
    rw [principal_neBot_iff]
    refine ⟨fun i => ((N : ℤ) + 1) * (i.val : ℤ), ?_, ?_⟩
    · intro a b hab
      have : (a.val : ℤ) < b.val := by exact_mod_cast hab
      have hN : (0 : ℤ) < (N : ℤ) + 1 := by positivity
      exact mul_lt_mul_of_pos_left this hN
    · intro i j hij
      simp only [hij]
      push_cast
      nlinarith

/-- Theorem 1.1 (explicit form). `T` invertible, measurable with measurable inverse
(`Ω ≃ᵐ Ω`), preserving the probability measure `μ`, and mixing. Then for every `k ≥ 3`
(written `k = j + 1`, `j ≥ 2`) and measurable `A₁, …, A_k`,
`μ(A₁ ∩ T^{-n₁}A₂ ∩ ⋯ ∩ T^{-(n₁+⋯+n_{k-1})}A_k) → ∏ μ(Aᵢ)`
as `min(n₁, …, n_{k-1}) → ∞` through positive integers. -/
theorem reading_thm_1_1 (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω ≃ᵐ Ω)
    (hT : MeasurePreserving T μ μ) (hmix : IsMixing μ T)
    (j : ℕ) (hj : 2 ≤ j) (A : Fin (j + 1) → Set Ω) (hA : ∀ i, MeasurableSet (A i)) :
    Tendsto (fun n : Fin j → ℕ => μ (⋂ i : Fin (j + 1), tPre T (partialSum n i) (A i)))
      (minAtTop j) (𝓝 (∏ i, μ (A i))) := sorry

/-- Theorem 1.1 (definition-level form): an invertible mixing probability-preserving
transformation is mixing of order `k` for every `k ≥ 2`. -/
theorem reading_thm_1_1_every_order (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω ≃ᵐ Ω)
    (hT : MeasurePreserving T μ μ) (hmix : IsMixing μ T) :
    ∀ k : ℕ, 2 ≤ k → IsMixingOfOrder μ T k := sorry

end ReaderA

/-
AMBIGUITIES AND CHOICES (reader A)

1. "Invertible measurable transformation with measurable inverse": `T : Ω ≃ᵐ Ω`
   (Mathlib `MeasurableEquiv`: bijection, both directions measurable). "Preserves μ":
   `MeasurePreserving T μ μ`. Probability space: `[IsProbabilityMeasure μ]` on an arbitrary
   measurable space (no standardness / countable generation, as the text insists).

2. Integer powers: `T^n` for `n ∈ ℤ` is the `n`-th power in the permutation group
   `Equiv.Perm Ω`; `T^{-n}B` is read as the preimage `(T^n)⁻¹(B)` (standard convention, and the
   only one under which `μ(A ∩ T^{-n}B)` and the order-k intersection match the displayed
   formulas). For `n ≥ 0` this is `{x | Tⁿ x ∈ B}`.

3. Measure values are kept in `ℝ≥0∞` (Mathlib's `μ s`), with convergence in the `ℝ≥0∞`
   topology. All values are ≤ 1 (finite), so this is equivalent to convergence of the real
   numbers; products `μ A * μ B`, `∏ μ(Aᵢ)` are in `ℝ≥0∞` with finite factors (no `⊤` issues).

4. "|n| → ∞" in the mixing definition: filter `comap (|·|) atTop` on `ℤ` (= cofinite on ℤ), i.e.
   both n → +∞ and n → −∞. This is the hypothesis as literally stated (two-sided).

5. Theorem 1.1 explicit form: `k ≥ 3` encoded as `k = j + 1` with `j ≥ 2`, so the
   `k − 1` gaps `n₁, …, n_{k−1}` are `n : Fin j → ℕ` with no ℕ subtraction. The exponent of
   `A_{i}` (1-based) is `n₁ + ⋯ + n_{i−1}`, implemented as `partialSum n i` = sum over `l < i`
   (0-based), an integer, so `A₁` gets exponent 0. "min(n₁,…,n_{k−1}) → ∞ through positive
   integers": filter `minAtTop j = ⨅ N, 𝓟 {n | all nᵢ > 0 ∧ all nᵢ ≥ N}`; positivity is
   automatic once N ≥ 1, kept for literalness. Proven `NeBot`, so the claim is not vacuous.

6. Mixing of order k (definition level): over `t : Fin k → ℤ` along
   `gapAtTop k = ⨅ N, 𝓟 {t | t strictly increasing ∧ every consecutive gap ≥ N}`, i.e.
   `t₁ < ⋯ < t_k` integers with `min_{i<k}(t_{i+1} − t_i) → ∞`; `t₁` is free (the remark
   "invariance allows t₁ = 0" is not built in). Proven `NeBot`. Stated for every `k ≥ 2`
   (k = 2 is essentially the one-sided half of the mixing hypothesis).

7. "for every A_i ∈ F": `MeasurableSet` hypotheses. The mixing hypothesis quantifies over
   measurable `A, B` only.

8. The paper's Corollary on endomorphisms/flows is outside the requested scope and not stated.
-/

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
