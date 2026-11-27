import Mathlib

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
