import Mathlib

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
