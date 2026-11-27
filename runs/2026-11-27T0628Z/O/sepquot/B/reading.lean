import Mathlib

open Cardinal ENNReal TopologicalSpace

universe u

namespace ReaderB

/-- `SQ 𝕜`: every infinite-dimensional Banach space over 𝕜 admits a bounded linear surjection
onto a separable infinite-dimensional Banach space. -/
def SQ (𝕜 : Type) [RCLike 𝕜] : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
    ¬ Module.Finite 𝕜 X →
      ∃ (Y : Type u) (_ : NormedAddCommGroup Y) (_ : NormedSpace 𝕜 Y) (_ : CompleteSpace Y),
        SeparableSpace Y ∧ ¬ Module.Finite 𝕜 Y ∧
        ∃ f : X →L[𝕜] Y, Function.Surjective f

/-- κ is real-valued measurable: uncountable, and there is a probability measure on all subsets of
a set of cardinality κ, vanishing on singletons, additive over disjoint families of size < κ
(sum = supremum of finite subsums = `tsum` in `ℝ≥0∞`). -/
def RealValuedMeasurable (κ : Cardinal.{u}) : Prop :=
  ℵ₀ < κ ∧ ∃ (α : Type u) (μ : Set α → ℝ≥0∞), #α = κ ∧ μ Set.univ = 1 ∧ (∀ a, μ {a} = 0) ∧
    ∀ (ι : Type u) (A : ι → Set α), #ι < κ → Pairwise (Function.onFun Disjoint A) →
      μ (⋃ i, A i) = ∑' i, μ (A i)

/-- Theorem 1.1 (i). -/
theorem reading_sepquot_i (𝕜 : Type) [RCLike 𝕜]
    (h : RealValuedMeasurable.{u} Cardinal.continuum.{u}) : SQ.{u} 𝕜 := sorry

/-- Theorem 1.1 (ii), CH as `2^ℵ₀ = ℵ₁`. -/
theorem reading_sepquot_ii (𝕜 : Type) [RCLike 𝕜]
    (h : (Cardinal.continuum.{u}) = aleph 1) : ¬ SQ.{u} 𝕜 := sorry

/-
Ambiguities / choices.
* 𝔽 ∈ {ℝ, ℂ}: `𝕜 : Type` with `[RCLike 𝕜]` (covers exactly ℝ and ℂ up to iso; instantiate
  with `ℝ`, `ℂ`).
* Universes: SQ is stated for Banach spaces in `Type u`, with the witness Y also in `Type u`
  (a quotient of X, so no loss); 𝔠 is `Cardinal.continuum.{u}`. The theorems hold for each u.
* Infinite-dimensional: `¬ Module.Finite 𝕜 X`. Banach: `NormedAddCommGroup`, `NormedSpace 𝕜`,
  `CompleteSpace`. Separable: `SeparableSpace`. Bounded linear surjection: `X →L[𝕜] Y` surjective.
  Existential over Y packs the instances explicitly. The "equivalently ... closed subspace M"
  formulation is not used.
* Real-valued measurable: stated literally from the excerpt, with no Mathlib `Measure` (which
  needs a σ-algebra and countable additivity only): μ : Set α → ℝ≥0∞ on *every* subset of a type
  α with #α = κ, μ univ = 1 (probability), μ {a} = 0, and for every disjoint family indexed by a
  type of cardinality < κ, μ(⋃) = ∑' (tsum in ℝ≥0∞ = sup of finite subsums). I also require
  κ uncountable (the excerpt's "uncountable cardinal κ"). Monotonicity/finite additivity follow.
  Index types are `Type u`, fine since #ι < κ ≤ Type u cardinals.
* CH: `continuum = aleph 1` (ℵ₁ = 2^ℵ₀) — Mathlib has no `CH` def here.
* Not stated: "if ZFC with a measurable cardinal is consistent then SQ is independent of ZFC",
  "consistency of failure needs only Con(ZFC)", and Corollary 1.2 (independence of SQ^{ℵ₁}).
  These are metamathematical statements about provability/consistency in ZFC and forcing
  models; Lean's logic cannot express consistency of ZFC or the existence of models of ZFC in
  a way that quantifies over theories (one could encode ZFC as a first-order theory in
  Mathlib's `FirstOrder` and state `¬ Theory.IsSatisfiable`/provability, but Mathlib has no
  ZFC theory, no definable SQ sentence, no forcing); so only the two ZFC implications
  (i), (ii) are stated, as theorems internal to Lean (whose axioms include Choice).
-/

end ReaderB
