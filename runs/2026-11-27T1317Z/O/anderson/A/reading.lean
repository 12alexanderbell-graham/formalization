import Mathlib

open MeasureTheory ProbabilityTheory

namespace ReaderA

/-- The Hilbert space `ℓ²(ℤ²)` of complex square-summable functions on `ℤ²`. -/
abbrev L2Z2 : Type := lp (fun _ : ℤ × ℤ => ℂ) 2

/-- The `ℓ¹` distance on `ℤ²`: `|y - x|₁ = |y₁ - x₁| + |y₂ - x₂|`. -/
def l1dist (x y : ℤ × ℤ) : ℤ := |y.1 - x.1| + |y.2 - x.2|

/-- The (finite) set of `y ∈ ℤ²` with `|y - x|₁ = 1`, i.e. the four lattice neighbours. -/
def nbrs (x : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  {(x.1 + 1, x.2), (x.1 - 1, x.2), (x.1, x.2 + 1), (x.1, x.2 - 1)}

/-- `H` is the Anderson operator `H_v` on `ℓ²(ℤ²)`:
`(H u)(x) = ∑_{|y-x|₁=1} u(y) + v_x u(x)` for every `u ∈ ℓ²(ℤ²)` and `x ∈ ℤ²`. -/
def IsAndersonOp (v : ℤ × ℤ → ℝ) (H : L2Z2 →L[ℂ] L2Z2) : Prop :=
  ∀ (u : L2Z2) (x : ℤ × ℤ), (H u) x = (∑ y ∈ nbrs x, u y) + (v x : ℂ) * u x

/-- The set of (complex) eigenvalues of `H`. -/
def eigenvalues (H : L2Z2 →L[ℂ] L2Z2) : Set ℂ :=
  {μ | ∃ u : L2Z2, u ≠ 0 ∧ H u = μ • u}

/-- The set of eigenvectors of `H` (nonzero `u` with `H u = μ u` for some `μ`). -/
def eigenvectors (H : L2Z2 →L[ℂ] L2Z2) : Set L2Z2 :=
  {u | u ≠ 0 ∧ ∃ μ : ℂ, H u = μ • u}

/-- The random-potential hypotheses: `(v_x)_{x ∈ ℤ²}` independent, each uniform on `[-h, h]`. -/
structure IsUniformIID {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (h : ℝ)
    (v : ℤ × ℤ → Ω → ℝ) : Prop where
  meas : ∀ x, Measurable (v x)
  indep : iIndepFun v P
  unif : ∀ x, P.map (v x) = ProbabilityTheory.cond volume (Set.Icc (-h) h)

/-- The interval `[-4-h, 4+h]` viewed inside `ℂ`. -/
def specInterval (h : ℝ) : Set ℂ := (fun t : ℝ => (t : ℂ)) '' Set.Icc (-4 - h) (4 + h)

/-- Theorem 1.1 (i): almost surely `σ(H_v) = [-4-h, 4+h]`. -/
theorem reading_thm_1_1_spectrum
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : ℝ) (hh : 0 < h) (v : ℤ × ℤ → Ω → ℝ) (hv : IsUniformIID P h v) :
    ∀ᵐ ω ∂P, ∃ H : L2Z2 →L[ℂ] L2Z2, IsAndersonOp (fun x => v x ω) H ∧
      spectrum ℂ H = specInterval h := sorry

/-- Theorem 1.1 (ii): almost surely `H_v` has pure-point spectral type
(the closed span of its eigenvectors is all of `ℓ²(ℤ²)`). -/
theorem reading_thm_1_1_purePoint
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : ℝ) (hh : 0 < h) (v : ℤ × ℤ → Ω → ℝ) (hv : IsUniformIID P h v) :
    ∀ᵐ ω ∂P, ∃ H : L2Z2 →L[ℂ] L2Z2, IsAndersonOp (fun x => v x ω) H ∧
      (Submodule.span ℂ (eigenvectors H)).topologicalClosure = ⊤ := sorry

/-- Theorem 1.1 (iii): almost surely `H_v` admits a complete orthonormal eigenbasis. -/
theorem reading_thm_1_1_eigenbasis
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : ℝ) (hh : 0 < h) (v : ℤ × ℤ → Ω → ℝ) (hv : IsUniformIID P h v) :
    ∀ᵐ ω ∂P, ∃ H : L2Z2 →L[ℂ] L2Z2, IsAndersonOp (fun x => v x ω) H ∧
      ∃ (ι : Type) (b : HilbertBasis ι ℂ L2Z2), ∀ i, ∃ μ : ℂ, H (b i) = μ • b i := sorry

/-- Theorem 1.1 (iv): almost surely the eigenvalues of `H_v` are dense in `[-4-h, 4+h]`
(they lie in it and their closure is all of it). -/
theorem reading_thm_1_1_denseEigenvalues
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : ℝ) (hh : 0 < h) (v : ℤ × ℤ → Ω → ℝ) (hv : IsUniformIID P h v) :
    ∀ᵐ ω ∂P, ∃ H : L2Z2 →L[ℂ] L2Z2, IsAndersonOp (fun x => v x ω) H ∧
      eigenvalues H ⊆ specInterval h ∧ specInterval h ⊆ closure (eigenvalues H) := sorry

end ReaderA

/-
Ambiguities and choices (Reader A):

1. Hilbert space: `ℓ²(ℤ²)` is taken complex, `lp (fun _ : ℤ × ℤ => ℂ) 2` (standard for
   Schrödinger operators); the spectrum is `spectrum ℂ H` in the Banach algebra of bounded
   operators, and `[-4-h, 4+h]` is embedded in `ℂ` via `ℝ → ℂ`. (A real ℓ² would give the same
   real spectrum for this self-adjoint real-symmetric operator.)
2. The operator: rather than constructing `H_v` as a `ContinuousLinearMap` (which would need a
   boundedness proof in a definition, and fails for unbounded `v`), I characterise it by the
   pointwise formula `IsAndersonOp v H` and state every conclusion as
   `∃ H, IsAndersonOp v H ∧ property H`. The formula determines `H` uniquely (evaluate at each
   coordinate), so the existential is not a loophole; and the existential forces `H_v` to be a
   bounded operator on `ℓ²`, which holds whenever `v` is bounded (a.s. here, since `v_x ∈ [-h,h]`
   a.s. and ℤ² is countable). The statement is therefore not vacuous.
3. `∑_{|y-x|₁=1}`: summed over the explicit finset of the four neighbours
   `(x₁±1, x₂), (x₁, x₂±1)`; these are pairwise distinct so the finset sum equals the sum over
   `{y : |y-x|₁ = 1}`. `l1dist` is defined for documentation but the neighbour finset is used.
4. Randomness: an arbitrary probability space `(Ω, P)` carrying `v : ℤ² → Ω → ℝ`, measurable,
   mutually independent (`iIndepFun`), each with law `cond volume (Icc (-h) h)` =
   `(2h)⁻¹ · Lebesgue|[-h,h]` (well-defined, nonzero since `h > 0`). Quantifying over all such
   spaces covers the canonical product space. "Almost surely" is `∀ᵐ ω ∂P` (the event need not be
   proved measurable — `∀ᵐ` means the failure set is contained in a null set). The event may
   depend on `h` (h is fixed before `∀ᵐ`), as the source allows.
5. "Pure-point spectral type" = closure of the (algebraic) span of the eigenvectors is `⊤`, as the
   source defines it. Eigenvectors are nonzero vectors with `H u = μ u` for some complex `μ`.
6. "Complete orthonormal eigenbasis" = a `HilbertBasis ι ℂ ℓ²(ℤ²)` (orthonormal with dense span)
   each of whose vectors is an eigenvector; index type in `Type` (ℓ²(ℤ²) is separable so a
   countable index suffices; no restriction imposed).
7. "Eigenvalues dense in this interval": eigenvalues (complex, a priori) lie in `[-4-h,4+h]` and
   their closure contains it. Stated as two inclusions so (iv) is self-contained, not relying on (i).
8. The four conclusions are separate theorems, each with its own a.s. event; the source's single
   event for all of them follows by intersecting four null complements.
9. Junk values: none (no division except inside `cond`, where `volume (Icc (-h) h) = 2h ≠ 0, ∞`).
-/
