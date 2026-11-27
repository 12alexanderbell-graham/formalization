import Mathlib

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
