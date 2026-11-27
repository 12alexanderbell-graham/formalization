import Mathlib

/-! Blind readings A, B, C (code unchanged; only `import Mathlib` hoisted). -/

-- ===== reader A =====

/-!
Blind reading A of O34, Theorem 1.1: there is a separable real Banach space `Z` with no closed
linear subspace isomorphic to `c₀`, and an onto bi-Lipschitz map `Z ⊕_∞ c₀ → Z`.
-/

namespace ReaderA

open Filter Topology ENNReal

/-- `c₀`: real sequences tending to zero, with the supremum norm. Realized as the subspace of
`ℓ^∞(ℕ, ℝ)` (Mathlib's `lp _ ∞`, whose norm is the supremum norm) of sequences tending to `0`. -/
def c0 : Submodule ℝ (lp (fun _ : ℕ => ℝ) ∞) where
  carrier := {f | Tendsto (fun n => f n) atTop (𝓝 0)}
  add_mem' := by
    intro a b ha hb
    have := ha.add hb
    simpa using this
  zero_mem' := by
    simp
  smul_mem' := by
    intro c a ha
    have := ha.const_smul c
    simpa using this

/-- Sanity check: the norm on `c₀` is the supremum norm. -/
example (f : c0) : ‖f‖ = ⨆ n, ‖(f : lp (fun _ : ℕ => ℝ) ∞) n‖ :=
  lp.norm_eq_ciSup _

/-- Sanity check: the product norm on `X × Y` is the `ℓ^∞`-sum norm `max ‖x‖ ‖y‖`. -/
example {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y] (x : X) (y : Y) :
    ‖(x, y)‖ = max ‖x‖ ‖y‖ := Prod.norm_def (x, y)

/-- Bi-Lipschitz embedding with constants `0 < c ≤ C < ∞`, as in the source. -/
def IsBiLipschitz {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y] (F : X → Y) :
    Prop :=
  ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
    ∀ x x' : X, c * ‖x - x'‖ ≤ ‖F x - F x'‖ ∧ ‖F x - F x'‖ ≤ C * ‖x - x'‖

/-- `Z` contains a closed linear subspace (linearly and topologically) isomorphic to `c₀`. -/
def ContainsC0 (Z : Type*) [NormedAddCommGroup Z] [NormedSpace ℝ Z] : Prop :=
  ∃ V : Submodule ℝ Z, IsClosed (V : Set Z) ∧ Nonempty (V ≃L[ℝ] c0)

/-- Theorem 1.1. `Z ⊕_∞ c₀` is the product `Z × c0`, whose norm is `max ‖z‖ ‖c‖`. -/
theorem reading_thm_1_1 :
    ∃ (Z : Type) (_ : NormedAddCommGroup Z) (_ : NormedSpace ℝ Z),
      CompleteSpace Z ∧ TopologicalSpace.SeparableSpace Z ∧ ¬ ContainsC0 Z ∧
      ∃ F : Z × c0 → Z, Function.Surjective F ∧ IsBiLipschitz F := sorry

end ReaderA

/-
AMBIGUITIES AND CHOICES

1. c₀. Defined by hand as the submodule of `lp (fun _ : ℕ => ℝ) ∞` of sequences tending to 0;
   it inherits the sup norm (checked by the first `example`). Real scalars, index set ℕ.
   (Mathlib also has `ZeroAtInftyContinuousMap ℕ ℝ`; I preferred an explicit definition.)
   Every sequence tending to 0 is bounded, so nothing is lost by sitting inside ℓ^∞.

2. Z ⊕_∞ c₀. Mathlib's product `Z × c0` carries exactly the norm `max ‖z‖ ‖c‖` (`Prod.norm_def`,
   checked by the second `example`), which is the source's definition of `⊕_∞`.

3. "Separable real Banach space": `NormedAddCommGroup Z`, `NormedSpace ℝ Z`, `CompleteSpace Z`,
   `SeparableSpace Z`. `Z : Type` (universe 0); a separable space lives there up to isometry.

4. "Closed linear subspace isomorphic to c₀": a `Submodule ℝ Z` that is closed, with a continuous
   linear isomorphism (`≃L[ℝ]`) onto `c₀` (Banach-space isomorphism, not necessarily isometric).
   Closedness is in fact automatic for a subspace isomorphic to a complete space, but I keep it
   since the source states it.

5. "Onto bi-Lipschitz map": the source's definition with constants `0 < c ≤ C < ∞`, plus
   surjectivity. No continuity or linearity assumed (continuity follows from the upper bound).
   Not required to be linear — that is the point of the theorem.

6. No junk values: all constants are explicitly quantified and positive; no division.
-/

-- ===== reader B =====

open ENNReal

namespace ReaderB

/-- `c₀`: real sequences tending to zero with the sup norm, realised as the subspace of
bounded sequences `lp (fun _ : ℕ => ℝ) ∞` (sup norm) of sequences tending to `0`. -/
def c0 : Submodule ℝ (lp (fun _ : ℕ => ℝ) ∞) where
  carrier := {a | Filter.Tendsto (fun n => (a : ℕ → ℝ) n) Filter.atTop (nhds 0)}
  zero_mem' := by simp [tendsto_const_nhds]
  add_mem' := by
    intro a b ha hb
    simpa using ha.add hb
  smul_mem' := by
    intro c a ha
    simpa using ha.const_mul c

/-- `c₀` as a normed space (subtype norm of the sup norm). -/
abbrev C0 := ↥c0

/-- `F` is an onto bi-Lipschitz map. -/
def IsBiLipschitzOnto {X Y : Type} [PseudoMetricSpace X] [PseudoMetricSpace Y] (F : X → Y) : Prop :=
  Function.Surjective F ∧ ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ x x' : X,
    c * dist x x' ≤ dist (F x) (F x') ∧ dist (F x) (F x') ≤ C * dist x x'

/-- The product `Z × c₀` in Mathlib carries the max norm, i.e. it is `Z ⊕_∞ c₀`. -/
theorem reading_c0absorb :
    ∃ (Z : Type) (_ : NormedAddCommGroup Z) (_ : NormedSpace ℝ Z),
      CompleteSpace Z ∧ TopologicalSpace.SeparableSpace Z ∧
      (∀ S : Submodule ℝ Z, IsClosed (S : Set Z) → IsEmpty (S ≃L[ℝ] C0)) ∧
      ∃ F : Z × C0 → Z, IsBiLipschitzOnto F := sorry

end ReaderB

/-
Ambiguities and choices.
* c₀ is built by me as a Submodule of `lp (fun _ => ℝ) ∞` (bounded sequences, sup norm), defined by
  Tendsto to 0; it inherits norm; it is complete (closed) but completeness isn't needed in the statement.
* Z ⊕_∞ c₀: Mathlib's `Prod` normed-group instance uses the max norm, exactly the source's norm
  max{‖x‖,‖y‖}; so I use `Z × C0` and the metric `dist` from that instance.
* "Banach space": NormedAddCommGroup + NormedSpace ℝ + CompleteSpace; separable = SeparableSpace.
  Z lives in `Type` (universe 0), fine since Z separable.
* "no closed linear subspace isomorphic to c₀": for every closed ℝ-submodule S of Z, no continuous
  linear equivalence S ≃L[ℝ] c₀ (isomorphism = linear homeomorphism, i.e. bounded with bounded inverse).
  S carries the subtype norm. The case S = ⊥ is fine since C0 is nontrivial.
* Bi-Lipschitz equivalence onto: surjective, and constants 0<c≤C with the two-sided inequality in `dist`,
  as in the source; injectivity follows from c>0. Constants real; 'c ≤ C' is included as in source.
* Junk avoided: no Option/default values; existential over Z with explicit instances (as separate
  existentials, so the instance used in `dist`, `S`, `Z × C0` is the one supplied).
-/

-- ===== reader C =====

namespace ReaderC

/-! Reading of O34: Theorem 1.1.

Definitions written from the source:
* All Banach spaces are real: `NormedSpace ℝ Z`, complete (`CompleteSpace`) and separable
  (`SeparableSpace`).
* c0 = c0(ℕ) = real sequences tending to zero with the sup norm. We use Mathlib's
  `ZeroAtInftyContinuousMap ℕ ℝ` = `ZeroAtInftyContinuousMap ℕ ℝ`: ℕ carries the discrete topology, so
  continuous maps tending to 0 at infinity are exactly the sequences tending to 0, with the
  sup norm (Mathlib's instance).
* "Linear subspace isomorphic to c0": a closed `Submodule ℝ Z` whose subtype is
  linearly and topologically isomorphic to c0, i.e. `Nonempty (Y ≃L[ℝ] ZeroAtInftyContinuousMap ℕ ℝ)`.
* X ⊕_∞ Y: Mathlib's product `Z × ZeroAtInftyContinuousMap ℕ ℝ`, whose norm is the max norm.
* Bi-Lipschitz equivalence: a surjective map F with constants 0 < c ≤ C < ∞ such that
  c·dist(x,x') ≤ dist(F x, F x') ≤ C·dist(x,x') for all x, x'. (dist is the metric induced
  by the norms, so ‖x - x'‖ = dist x x'.)

Ambiguities and choices:
* "Banach space" is read as a real complete normed space; the existential over Z is
  formulated with explicit instance binders so Z is a genuine real Banach space.
* Isomorphism of c0 with a subspace is a linear homeomorphism (`≃L[ℝ]`), not merely a
  bounded linear bijection; for Banach spaces these are the same (open mapping), so no
  information is lost.
* The theorem's existential asserts there is some Z with all listed properties at once.
-/

/-- Theorem 1.1: there is a separable real Banach space Z with no closed linear subspace
isomorphic to c0 and an onto bi-Lipschitz map Z ⊕_∞ c0 → Z. -/
theorem reading_c0absorb_thm11 :
    ∃ (Z : Type) (_ : NormedAddCommGroup Z) (_ : NormedSpace ℝ Z),
      CompleteSpace Z ∧ TopologicalSpace.SeparableSpace Z ∧
      ¬ (∃ Y : Submodule ℝ Z, IsClosed (Y : Set Z) ∧ Nonempty (Y ≃L[ℝ] ZeroAtInftyContinuousMap ℕ ℝ)) ∧
      ∃ F : Z × ZeroAtInftyContinuousMap ℕ ℝ → Z, Function.Surjective F ∧
        ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
          ∀ x y : Z × ZeroAtInftyContinuousMap ℕ ℝ,
            c * dist x y ≤ dist (F x) (F y) ∧ dist (F x) (F y) ≤ C * dist x y := by
  sorry

end ReaderC
