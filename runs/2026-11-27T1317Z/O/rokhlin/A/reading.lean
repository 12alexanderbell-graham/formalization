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
