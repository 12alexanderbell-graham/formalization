import Mathlib

/-!
Reading C of O31: "Relative independence of the separable quotient problem" (only the excerpt
`sepquot/sources/introduction_lines1-56.tex` was read).
-/

open Cardinal

namespace ReaderC

/-- "`Y` is a separable infinite-dimensional Banach space" and "`X` admits a bounded linear
surjection onto `Y`", packaged as: `X` has a separable infinite-dimensional Banach quotient. -/
def HasSepInfQuot (𝕜 : Type) [RCLike 𝕜] (X : Type) [NormedAddCommGroup X] [NormedSpace 𝕜 X] :
    Prop :=
  ∃ (Y : Type) (_ : NormedAddCommGroup Y) (_ : NormedSpace 𝕜 Y),
    CompleteSpace Y ∧ TopologicalSpace.SeparableSpace Y ∧ ¬ FiniteDimensional 𝕜 Y ∧
      ∃ T : X →L[𝕜] Y, Function.Surjective T

/-- `SQ_𝕜`: every infinite-dimensional Banach space over `𝕜` admits a bounded linear surjection
onto a separable infinite-dimensional Banach space. -/
def SQ (𝕜 : Type) [RCLike 𝕜] : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
    ¬ FiniteDimensional 𝕜 X → HasSepInfQuot 𝕜 X

/-- Norm density of a normed space: the least cardinality of a norm-dense subset.
The set of such cardinals is nonempty (the whole space is dense), so `sInf` is not junk. -/
noncomputable def normDensity (X : Type) [NormedAddCommGroup X] : Cardinal :=
  sInf {κ : Cardinal | ∃ D : Set X, Dense D ∧ Cardinal.mk D = κ}

/-- `SQ^{ℵ₁}_𝕜`: every Banach space over `𝕜` of norm density exactly `ℵ₁` has a separable
infinite-dimensional quotient. -/
def SQ1 (𝕜 : Type) [RCLike 𝕜] : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
    normDensity X = Cardinal.aleph 1 → HasSepInfQuot 𝕜 X

/-- `κ` is real-valued measurable: there is a set `ι` of cardinality `κ` and a probability
measure on all subsets of `ι` (values in `ℝ≥0∞`), vanishing on singletons, which is
`κ`-additive: for every family `(A i)_{i : I}` of pairwise disjoint sets with `#I < κ`, the
measure of the union is the supremum of the finite subsums. -/
def RealValuedMeasurable (κ : Cardinal.{0}) : Prop :=
  ∃ ι : Type, Cardinal.mk ι = κ ∧
    ∃ μ : Set ι → ENNReal,
      μ Set.univ = 1 ∧
      (∀ x : ι, μ {x} = 0) ∧
      ∀ (I : Type) (A : I → Set ι), Cardinal.mk I < κ →
        Pairwise (fun i j => Disjoint (A i) (A j)) →
        μ (⋃ i, A i) = ⨆ F : Finset I, ∑ i ∈ F, μ (A i)

/-- Theorem 1.1 (i): if `𝔠` is real-valued measurable, then `SQ_𝔽` holds (for `𝔽 ∈ {ℝ, ℂ}`). -/
theorem reading_sepquot_thm11_i (𝕜 : Type) [RCLike 𝕜] (hF : 𝕜 = ℝ ∨ 𝕜 = ℂ)
    (h : RealValuedMeasurable Cardinal.continuum) :
    SQ 𝕜 := by
  sorry

/-- Theorem 1.1 (ii): if the continuum hypothesis `2^ℵ₀ = ℵ₁` holds, then `SQ_𝔽` fails
(for `𝔽 ∈ {ℝ, ℂ}`). -/
theorem reading_sepquot_thm11_ii (𝕜 : Type) [RCLike 𝕜] (hF : 𝕜 = ℝ ∨ 𝕜 = ℂ)
    (hCH : Cardinal.continuum = Cardinal.aleph 1) :
    ¬ SQ 𝕜 := by
  sorry

end ReaderC

/-
Ambiguities and choices (Reader C, O31):

1. Scalars: `𝔽 ∈ {ℝ, ℂ}` is `𝕜 : Type` with `[RCLike 𝕜]` and hypothesis `𝕜 = ℝ ∨ 𝕜 = ℂ`
   (the only RCLike instances in Mathlib are these, so the hypothesis is what restricts
   to the excerpt's two fields). `SQ 𝕜` is defined for any `RCLike 𝕜`, and the theorems
   restrict to ℝ, ℂ.
2. Banach spaces are `Type`-valued (universe 0). This is a restriction: the excerpt does not
   fix a universe. Spaces of larger size (in universes > 0) are not quantified over in
   `SQ`; this is a choice made to keep the statement in one universe.
3. Infinite-dimensional: `¬ FiniteDimensional 𝕜 X`. Separable: `TopologicalSpace.SeparableSpace`.
   Banach: `NormedAddCommGroup` + `NormedSpace 𝕜` + `CompleteSpace`.
4. "Bounded linear surjection onto a separable infinite-dimensional Banach space":
   `∃ T : X →L[𝕜] Y, Function.Surjective T` with `Y` complete (Banach), separable and
   `¬ FiniteDimensional 𝕜 Y`. The target `Y` is existentially quantified together with its
   normed-space instances (`HasSepInfQuot`). Continuous linear maps are bounded, the standard
   reading.
5. The excerpt's equivalent formulation (closed subspace M with X/M separable infinite-dim)
   is not used; the surjection form is the one in the displayed statement of SQ.
6. Real-valued measurable: the measure is `Set ι → ENNReal` on all subsets of a type `ι` of
   cardinality `κ` (equivalently a measure on `P(κ)`). Probability: `μ univ = 1`. Vanishing on
   singletons: `μ {x} = 0`. `κ`-additivity: for every indexed family of pairwise disjoint sets
   with index type `I` of cardinality `< κ`, `μ(⋃ A i) = sup over finite F ⊆ I of Σ_{i∈F} μ(A i)`,
   the sup being the excerpt's "supremum of its finite subsums". `ENNReal` is used so that
   the supremum is always defined (no `sSup`-junk on unbounded sets); since `μ univ = 1` the
   values lie in [0,1] anyway. The index type `I : Type` (universe 0) matches `κ : Cardinal.{0}`.
   The excerpt's "real-valued" refers to the values of the measure; `ENNReal`-valued is the
   standard Lean encoding, and values above 1 are excluded by additivity plus `μ univ = 1`.
7. `𝔠 = Cardinal.continuum` (= 2^ℵ₀). The hypothesis "measure on every subset of 𝔠" is the
   `ι` with `#ι = 𝔠` quantifier in `RealValuedMeasurable`.
8. CH: `2^ℵ₀ = ℵ₁`, written `Cardinal.continuum = Cardinal.aleph 1`, with `Cardinal.aleph 1`
   the first infinite cardinal `ℵ₁`.
9. Theorem 1.1 (i) and (ii) are separate theorems, each with its own `𝕜` and `hF`. The
   excerpt's phrase "ZFC proves the following implications" is not formalized as a provability
   statement (see 11); the theorems say the implications themselves.
10. Norm density: `normDensity X = sInf {κ | ∃ D dense in X with #D = κ}`. Junk check: the set is
    nonempty (`univ` is dense), so `sInf` is the genuine minimum and not `sInf ∅ = 0`.
    `SQ1` is the excerpt's `SQ^{ℵ₁}_𝔽` with "norm density exactly ℵ₁" as
    `normDensity X = Cardinal.aleph 1`. Defined here, with no theorem about it (the excerpt
    refers to a later corollary `twist:density` for CH counterexamples at density ℵ₁, which is
    not in the excerpt and was not formalized).
11. NOT stated in Lean: the consistency and independence conclusions of Theorem 1.1 and
    Corollary 1.2 ("if ZFC with a measurable cardinal is consistent, then SQ_𝔽 is independent
    of ZFC", "consistency of its failure requires only consistency of ZFC", and the
    corollary "if ZFC is consistent, then SQ^{ℵ₁}_𝔽 is independent of ZFC"). Lean/Mathlib has
    no formal provability relation for ZFC (no `ZFC ⊢ φ` predicate over the Lean encodings of
    sentences), so "independent of ZFC" cannot be written as a Lean proposition here. Stating
    it would need a formalized first-order ZFC and its proof system (e.g. a model-theoretic
    `consistency` / forcing development), which is out of scope for this reading.
    The conditional parts can be expressed as implications between Lean propositions, but
    without a provability predicate they are not the independence claims.
12. Corollary 1.2 (SQ^{ℵ₁} independence): as in 11, the independence part is not stateable.
    The defined object `SQ1` is given so the claim's subject matter is in the file.
-/
