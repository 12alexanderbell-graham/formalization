import Mathlib

namespace ReaderB

open MeasureTheory ProbabilityTheory Set

/-- The Hilbert space ℓ²(ℤ²) over ℂ. -/
noncomputable abbrev L2Z2 := lp (fun _ : ℤ × ℤ => ℂ) 2

/-- The four nearest neighbour offsets (ℓ¹ distance 1). -/
def nbrs : Finset (ℤ × ℤ) := {(1, 0), (-1, 0), (0, 1), (0, -1)}

/-- `H` is the operator `H_v`: `(H u)(x) = ∑_{|y-x|₁=1} u(y) + v_x u(x)`. -/
def IsAnderson (v : ℤ × ℤ → ℝ) (H : L2Z2 →L[ℂ] L2Z2) : Prop :=
  ∀ (u : L2Z2) (x : ℤ × ℤ), H u x = ∑ e ∈ nbrs, u (x + e) + (v x : ℂ) * u x

/-- The uniform law on `[-h,h]`. -/
noncomputable def unif (h : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (2 * h))⁻¹ • volume.restrict (Icc (-h) h)

/-- Random potential: independent, each uniform on [-h,h]. -/
structure IsRandomPotential {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (h : ℝ)
    (v : ℤ × ℤ → Ω → ℝ) : Prop where
  meas : ∀ x, Measurable (v x)
  indep : iIndepFun v P
  law : ∀ x, P.map (v x) = unif h

noncomputable def eigenvalueSet (H : L2Z2 →L[ℂ] L2Z2) : Set ℝ :=
  {t | ∃ u : L2Z2, u ≠ 0 ∧ H u = (t : ℂ) • u}

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (h : ℝ) (hh : 0 < h) (v : ℤ × ℤ → Ω → ℝ) (hv : IsRandomPotential P h v)

include hh hv in
theorem readingSpectrum :
    ∀ᵐ ω ∂P, ∀ H : L2Z2 →L[ℂ] L2Z2, IsAnderson (fun x => v x ω) H →
      spectrum ℂ H = ((↑) : ℝ → ℂ) '' Icc (-4 - h) (4 + h) := sorry

include hh hv in
theorem readingPurePoint :
    ∀ᵐ ω ∂P, ∀ H : L2Z2 →L[ℂ] L2Z2, IsAnderson (fun x => v x ω) H →
      (Submodule.span ℂ {u : L2Z2 | ∃ μ : ℂ, H u = μ • u}).topologicalClosure = ⊤ := sorry

include hh hv in
theorem readingEigenbasis :
    ∀ᵐ ω ∂P, ∀ H : L2Z2 →L[ℂ] L2Z2, IsAnderson (fun x => v x ω) H →
      ∃ (ι : Type) (b : HilbertBasis ι ℂ L2Z2), ∀ i, ∃ μ : ℂ, H (b i) = μ • b i := sorry

include hh hv in
theorem readingDense :
    ∀ᵐ ω ∂P, ∀ H : L2Z2 →L[ℂ] L2Z2, IsAnderson (fun x => v x ω) H →
      eigenvalueSet H ⊆ Icc (-4 - h) (4 + h) ∧ Icc (-4 - h) (4 + h) ⊆ closure (eigenvalueSet H) :=
  sorry
end

end ReaderB

/-
Ambiguities / choices.
* Probability space: abstract (Ω, P) with v : ℤ² → Ω → ℝ, measurable, iIndepFun, law = normalized
  Lebesgue on [-h,h] (unif h; (2h)⁻¹ with hh : 0 < h, so no 1/0 junk). hh is included in every theorem.
* H_v is not constructed; "H is H_v" is the predicate IsAnderson and the theorems say: almost surely
  every bounded operator H on ℓ²(ℤ²) satisfying the formula has the property. For bounded v such an H
  exists and is unique, so not vacuous, but the statement does not itself assert existence.
* Hilbert space is over ℂ (needed for spectrum); ℓ²(ℤ²) = lp (fun _ => ℂ) 2. Potential real, cast.
* Spectrum: spectrum ℂ H equals image of real interval under ofReal.
* Pure point: closure of the span of {u | ∃ μ, H u = μ u} (includes u=0, harmless) = ⊤.
* Eigenbasis: exists index type ι : Type and Hilbert basis b all of whose members are eigenvectors
  (eigenvalue may be complex a priori; norm-one so nonzero automatically). Countability of ι is
  automatic by separability.
* Density: eigenvalues (real) lie in the interval and interval ⊆ closure of eigenvalues. Eigenvalues of
  self-adjoint H are real, so restricting to real eigenvalues loses nothing.
* The null event may depend on h (as in the source): ∀ᵐ is inside, h fixed outside.
* No ℕ subtraction, no junk division, no sSup used.
-/
