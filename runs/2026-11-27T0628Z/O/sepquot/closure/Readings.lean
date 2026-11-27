import Mathlib

/-! Blind readings A, B, C (code unchanged; only `import Mathlib` hoisted). -/

-- ===== reader A =====

/-!
# Blind reading A of O31: "Relative independence of the separable quotient problem"

Source: `sepquot/sources/introduction_lines1-56.tex`, definition of `SQ_𝔽`, Theorem 1.1 (i), (ii),
and (in comments) the consistency/independence conclusions and Corollary 1.2.
-/

namespace ReaderA

universe u

open Cardinal

/-- `SQ_𝔽`: "Every infinite-dimensional Banach space over `𝔽` admits a bounded linear surjection
onto a separable infinite-dimensional Banach space."
Banach spaces `X` range over `Type u`; the target `Y` is taken in the same universe.
The source only uses `𝔽 ∈ {ℝ, ℂ}`; the definition is written for any nontrivially normed field
and instantiated at `ℝ` and `ℂ` below. -/
def SQ (𝔽 : Type) [NontriviallyNormedField 𝔽] : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace 𝔽 X] [CompleteSpace X],
    ¬ FiniteDimensional 𝔽 X →
    ∃ (Y : Type u) (_ : NormedAddCommGroup Y) (_ : NormedSpace 𝔽 Y) (_ : CompleteSpace Y),
      TopologicalSpace.SeparableSpace Y ∧ ¬ FiniteDimensional 𝔽 Y ∧
      ∃ T : X →L[𝔽] Y, Function.Surjective T

/-- A probability measure `μ` on `𝒫(X)` (all subsets of `X`) is `κ`-additive: it is additive on
pairwise disjoint families of cardinality strictly less than `κ`, where the sum over such a family
means the supremum of its finite subsums. Values are in `[0, ∞]`; total mass `1`. -/
def IsKappaAdditiveProb {X : Type u} (κ : Cardinal.{u}) (μ : Set X → ENNReal) : Prop :=
  μ Set.univ = 1 ∧
  ∀ 𝒜 : Set (Set X), #𝒜 < κ → 𝒜.PairwiseDisjoint id →
    μ (⋃₀ 𝒜) = ⨆ F : Finset 𝒜, ∑ A ∈ F, μ (A : Set X)

/-- `κ` is real-valued measurable: `κ` is an uncountable cardinal and (a set of cardinality) `κ`
carries a `κ`-additive probability measure on all of its subsets vanishing on singletons. -/
def IsRealValuedMeasurable (κ : Cardinal.{u}) : Prop :=
  ℵ₀ < κ ∧ ∃ (X : Type u) (μ : Set X → ENNReal),
    #X = κ ∧ IsKappaAdditiveProb κ μ ∧ ∀ x : X, μ {x} = 0

/-- The continuum hypothesis: `𝔠 = ℵ₁`. -/
def CH : Prop := Cardinal.continuum.{0} = ℵ₁

/-- Theorem 1.1 (i): if `𝔠` is real-valued measurable, then `SQ_𝔽` holds, for `𝔽 = ℝ` and
`𝔽 = ℂ`. -/
theorem reading_i (h : IsRealValuedMeasurable Cardinal.continuum.{0}) :
    SQ.{u} ℝ ∧ SQ.{u} ℂ := sorry

/-- Theorem 1.1 (ii): if the continuum hypothesis holds, then `SQ_𝔽` fails, for `𝔽 = ℝ` and
`𝔽 = ℂ`. -/
theorem reading_ii (h : CH) : ¬ SQ.{u} ℝ ∧ ¬ SQ.{u} ℂ := sorry

/-- Norm density of a normed space: the least cardinality of a dense subset. (`Set.univ` is dense,
so the infimum is over a nonempty family and is attained.) -/
noncomputable def normDensity (X : Type u) [NormedAddCommGroup X] : Cardinal.{u} :=
  ⨅ s : {s : Set X // Dense s}, #s.1

/-- `SQ^{ℵ₁}_𝔽`: every Banach space over `𝔽` of norm density exactly `ℵ₁` has a separable
infinite-dimensional quotient, i.e. a closed subspace `M` with `X ⧸ M` separable and infinite
dimensional. Only a definition: Corollary 1.2 is not stated (see the comments below). -/
def SQaleph1 (𝔽 : Type) [NontriviallyNormedField 𝔽] : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace 𝔽 X] [CompleteSpace X],
    normDensity X = ℵ₁ →
    ∃ M : Submodule 𝔽 X, IsClosed (M : Set X) ∧
      TopologicalSpace.SeparableSpace (X ⧸ M) ∧ ¬ FiniteDimensional 𝔽 (X ⧸ M)

end ReaderA

/-!
## Ambiguities and choices

1. *`SQ_𝔽`, surjection vs quotient form.* The excerpt's defining sentence is the surjection form
   ("admits a bounded linear surjection onto a separable infinite-dimensional Banach space"), so
   `SQ` uses it: a continuous linear map `X →L[𝔽] Y` (bounded = continuous for linear maps between
   normed spaces) that is surjective. The excerpt notes it is equivalent (open mapping theorem) to
   the quotient form; I used the quotient form only for `SQ^{ℵ₁}`, whose wording is "has a separable
   infinite-dimensional quotient".
2. *"Infinite-dimensional"* = `¬ FiniteDimensional 𝔽 X` (algebraic dimension infinite), the standard
   meaning; for Banach spaces it agrees with every other reasonable reading.
3. *Universes.* "Every Banach space" is quantified over `X : Type u`, for an arbitrary universe
   `u`, and the theorems are stated for every `u`. The target `Y` lives in the same universe
   (any quotient `X ⧸ M` does; and a separable Banach space has cardinality `≤ 𝔠`, so it has a copy
   in every universe — the choice is immaterial). The cardinal hypotheses are about
   `𝔠 : Cardinal.{0}`; real-valued measurability and CH are invariant under lifting, so fixing
   universe `0` there is harmless.
4. *`𝔽 ∈ {ℝ, ℂ}`.* `SQ` is defined for a general nontrivially normed field and the theorems
   are stated as conjunctions for the literal fields `ℝ` and `ℂ`.
5. *Real-valued measurable (as the excerpt defines it, not Mathlib's notion).*
   - "probability measure on `𝒫(κ)`": a function `μ : Set X → ENNReal` on *all* subsets of a type
     `X` with `#X = κ`, with `μ univ = 1`. I quantify over all such `X` (∃); the notion is
     invariant under bijections, so this is the same as using `κ` itself as an ordinal/set.
   - "`κ`-additive: additive on pairwise disjoint families of cardinality `< κ`, the sum meaning
     the supremum of finite subsums": families are *sets* of subsets `𝒜 : Set (Set X)` with
     `#𝒜 < κ` and pairwise disjoint; `μ (⋃₀ 𝒜) = ⨆ (F : Finset 𝒜), ∑_{A ∈ F} μ A`, literally
     the supremum of finite subsums. Using `ENNReal` avoids the junk `⨆` of an unbounded set in
     `ℝ`; nonetheless all values are in fact in `[0,1]` (apply additivity to `{A, Aᶜ}`), and
     `μ ∅ = 0` (apply it to `{∅, univ}`). No separate finite-additivity axiom is needed: finite
     families have cardinality `< κ` since `κ` is uncountable. (Indexing families by sets rather
     than by indexed families only loses repetitions, which can only be repetitions of `∅`.)
   - "for an uncountable cardinal `κ`" is part of the definition: `ℵ₀ < κ`.
   - "vanishing on singletons": `μ {x} = 0` for all `x`.
6. *CH.* Read as the cardinal equation `𝔠 = ℵ₁` with Mathlib's `Cardinal.continuum` (`2^ℵ₀`, as
   the excerpt writes `𝔠 = 2^{ℵ₀}`) and `ℵ₁ = aleph 1`. Equivalent to "every infinite subset of
   ℝ is countable or has cardinality `𝔠`".
7. *Norm density.* The least cardinality of a norm-dense subset, written as an `⨅` over dense sets
   (nonempty index since `univ` is dense, so no junk `⨅ ∅`).

## Why the metamathematical conclusions are not stated

- "ZFC proves the following implications": a Lean theorem is a proof in Lean's type theory
  (consistency strength of ZFC plus countably many inaccessibles, because of universes), not
  literally a ZFC proof. The readings `reading_i`, `reading_ii` state the *mathematical*
  implications, which is all one can state internally.
- "Consequently, if ZFC + a measurable cardinal is consistent, then `SQ_𝔽` is independent of ZFC.
  Consistency of its failure requires only Con(ZFC)." and Corollary 1.2 ("If ZFC is consistent,
  then `SQ^{ℵ₁}_𝔽` is independent of ZFC") are statements about first-order provability in ZFC.
  Stating them in Lean requires a *deep embedding*: a first-order language of set theory, the
  theory ZFC as a set of sentences, a formalised provability/consistency predicate, and a
  first-order sentence that encodes `SQ_𝔽` (with Banach spaces, ℝ, ℂ, … coded as sets) together
  with a proof that the encoding means what `SQ` means. Mathlib's `ModelTheory` provides first-order
  languages, theories and satisfiability, but no ZFC theory, no coding of analysis inside it and no
  forcing, so these conclusions cannot be stated faithfully with Mathlib alone and I do not state
  them. (Inside Lean one also cannot say "`SQ` is independent" as a theorem about `SQ` itself: Lean
  proves either a statement or not; independence is a statement about a formal system.)
  I give `SQaleph1` as a definition only so that the object of Corollary 1.2 is pinned down.
-/

-- ===== reader B =====

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

-- ===== reader C =====

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
