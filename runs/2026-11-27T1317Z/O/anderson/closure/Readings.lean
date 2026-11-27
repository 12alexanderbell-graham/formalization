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

open MeasureTheory ProbabilityTheory

namespace ReaderC

/-- The Hilbert space `ℓ²(ℤ²)` over `ℂ`. -/
noncomputable abbrev L2Z2 := lp (fun _ : ℤ × ℤ => ℂ) (2 : ENNReal)

/-- Sum of the four nearest-neighbour values of `u` around `x` (the terms with `|y - x|₁ = 1`). -/
def adjSum (u : ℤ × ℤ → ℂ) (x : ℤ × ℤ) : ℂ :=
  u (x.1 + 1, x.2) + u (x.1 - 1, x.2) + u (x.1, x.2 + 1) + u (x.1, x.2 - 1)

/-- The uniform distribution on `[-h, h]`, as a measure on `ℝ`. -/
noncomputable def unifLaw (h : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (2 * h))⁻¹ • volume.restrict (Set.Icc (-h) h)

/-- `P` is a law under which the coordinates `(v_x)_{x ∈ ℤ²}` are i.i.d. uniform on `[-h, h]`. -/
def IIDUniform (h : ℝ) (P : Measure (ℤ × ℤ → ℝ)) : Prop :=
  IsProbabilityMeasure P ∧ (∀ x : ℤ × ℤ, P.map (fun ω => ω x) = unifLaw h) ∧
    iIndepFun (fun (x : ℤ × ℤ) (ω : ℤ × ℤ → ℝ) => ω x) P

/-- Theorem 1.1, conclusion (i): spectrum equals `[-4-h, 4+h]` almost surely.
`H` is the family of operators `H_v`, pinned down by the matrix formula on bounded `v`. -/
theorem reading_anderson_i (H : (ℤ × ℤ → ℝ) → (L2Z2 →L[ℂ] L2Z2))
    (hH : ∀ (h : ℝ) (v : ℤ × ℤ → ℝ), (∀ x, |v x| ≤ h) → ∀ (u : L2Z2) (x : ℤ × ℤ),
      ((H v u : L2Z2) : ℤ × ℤ → ℂ) x = adjSum (u : ℤ × ℤ → ℂ) x + (v x : ℂ) * (u : ℤ × ℤ → ℂ) x) :
    ∀ h : ℝ, 0 < h → ∀ P : Measure (ℤ × ℤ → ℝ), IIDUniform h P →
      ∀ᵐ ω ∂P, spectrum ℂ (H ω) = Complex.ofReal '' Set.Icc (-4 - h) (4 + h) := by
  sorry

/-- Theorem 1.1, conclusion (ii): almost surely pure-point spectral type, i.e. the closed span of
the eigenvectors is all of `ℓ²(ℤ²)`. -/
theorem reading_anderson_ii (H : (ℤ × ℤ → ℝ) → (L2Z2 →L[ℂ] L2Z2))
    (hH : ∀ (h : ℝ) (v : ℤ × ℤ → ℝ), (∀ x, |v x| ≤ h) → ∀ (u : L2Z2) (x : ℤ × ℤ),
      ((H v u : L2Z2) : ℤ × ℤ → ℂ) x = adjSum (u : ℤ × ℤ → ℂ) x + (v x : ℂ) * (u : ℤ × ℤ → ℂ) x) :
    ∀ h : ℝ, 0 < h → ∀ P : Measure (ℤ × ℤ → ℝ), IIDUniform h P →
      ∀ᵐ ω ∂P,
        (Submodule.span ℂ {u : L2Z2 | u ≠ 0 ∧ ∃ μ : ℂ, H ω u = μ • u}).topologicalClosure = ⊤ := by
  sorry

/-- Theorem 1.1, conclusion (iii): almost surely there is a complete orthonormal basis of
`ℓ²(ℤ²)` consisting of eigenvectors of `H_v`. -/
theorem reading_anderson_iii (H : (ℤ × ℤ → ℝ) → (L2Z2 →L[ℂ] L2Z2))
    (hH : ∀ (h : ℝ) (v : ℤ × ℤ → ℝ), (∀ x, |v x| ≤ h) → ∀ (u : L2Z2) (x : ℤ × ℤ),
      ((H v u : L2Z2) : ℤ × ℤ → ℂ) x = adjSum (u : ℤ × ℤ → ℂ) x + (v x : ℂ) * (u : ℤ × ℤ → ℂ) x) :
    ∀ h : ℝ, 0 < h → ∀ P : Measure (ℤ × ℤ → ℝ), IIDUniform h P →
      ∀ᵐ ω ∂P, ∃ (ι : Type) (b : HilbertBasis ι ℂ L2Z2),
        ∀ i : ι, ∃ μ : ℂ, H ω (b i) = μ • b i := by
  sorry

/-- Theorem 1.1, conclusion (iv): almost surely the eigenvalues of `H_v` are dense in
`[-4-h, 4+h]`: every point of the interval is a limit of eigenvalues. -/
theorem reading_anderson_iv (H : (ℤ × ℤ → ℝ) → (L2Z2 →L[ℂ] L2Z2))
    (hH : ∀ (h : ℝ) (v : ℤ × ℤ → ℝ), (∀ x, |v x| ≤ h) → ∀ (u : L2Z2) (x : ℤ × ℤ),
      ((H v u : L2Z2) : ℤ × ℤ → ℂ) x = adjSum (u : ℤ × ℤ → ℂ) x + (v x : ℂ) * (u : ℤ × ℤ → ℂ) x) :
    ∀ h : ℝ, 0 < h → ∀ P : Measure (ℤ × ℤ → ℝ), IIDUniform h P →
      ∀ᵐ ω ∂P, ∀ r ∈ Set.Icc (-4 - h) (4 + h), ∀ ε : ℝ, 0 < ε →
        ∃ μ : ℂ, (∃ u : L2Z2, u ≠ 0 ∧ H ω u = μ • u) ∧ ‖μ - (r : ℂ)‖ < ε := by
  sorry

end ReaderC

/-
Comment block: ambiguities and choices.

1. Space: `ℓ²(ℤ²)` is taken over `ℂ` (`lp (fun _ : ℤ × ℤ => ℂ) 2`). The source does not fix the
   scalar field; over `ℝ` the statements would be the same in substance. Eigen-statements use
   `μ : ℂ` and `H ω u = μ • u`.

2. The operator: the source defines `H_v` by a matrix formula. Mathlib has no direct
   construction of a bounded operator from such a formula without a boundedness proof, so `H` is a
   parameter with hypothesis `hH`: for every bounded `v` (|v x| ≤ h, which holds almost surely
   under the uniform law) and every `u ∈ ℓ²`, `(H v u) x = adjSum u x + v x * u x`. An operator on
   ℓ² is determined by its values, so `hH` pins down `H v` for every bounded `v`. The formula is
   written with explicit neighbours `(x₁±1, x₂)`, `(x₁, x₂±1)`; this is exactly the set
   `{y | |y - x|₁ = 1}`. The sum is finite, so there is no tsum. Values of `H ω` for unbounded
   `ω` are unconstrained, which is harmless because the statements are almost sure.

3. Randomness: `P` is a probability measure on `ℤ² → ℝ` (product σ-algebra) under which the
   coordinate maps are independent (`iIndepFun`) and each has law `unifLaw h`. This avoids
   `Measure.infinitePi`, whose definition needs a probability instance that cannot be supplied
   inside the statement without a proof term. The `IIDUniform h P` hypothesis is the
   source's "v_x iid uniform on [-h, h]". `unifLaw h` is `(2h)⁻¹` times Lebesgue measure on
   `[-h, h]`; it is a probability measure for `h > 0`, and `h > 0` is assumed in each theorem.

4. "For each h > 0, almost surely": each theorem is `∀ h > 0, ∀ P (iid law), ∀ᵐ ω ∂P, ...`, so
   the probability-one event may depend on h, as the source allows. Each of the four conclusions
   is a separate theorem.

5. (i) Spectrum: `spectrum ℂ (H ω)` equals the image of `[-4-h, 4+h]` under `Complex.ofReal`.
   The spectrum is a subset of ℂ, so the real interval is embedded.

6. (ii) Pure-point spectral type: the closed linear span of all nonzero eigenvectors (over
   ℂ, with any eigenvalue μ ∈ ℂ) is `⊤`. The span is taken in ℓ² with `topologicalClosure`.

7. (iii) Complete orthonormal eigenbasis: a Mathlib `HilbertBasis ι ℂ L2Z2` (an orthonormal
   basis, i.e. an isometric identification with ℓ²(ι)) whose members are eigenvectors. The index
   type `ι` is existentially quantified in `Type`. Each basis vector `b i` is an eigenvector
   (`H ω (b i) = μ • b i` for some `μ`). Eigenvectors are nonzero automatically in an orthonormal
   basis, since they have norm 1.

8. (iv) Density: the set of eigenvalues `{μ | ∃ u ≠ 0, H u = μ u}` is dense in `[-4-h, 4+h]`
   in the sense that each point `r` of the interval is approximated within any `ε > 0` by an
   eigenvalue. The eigenvalues are real (self-adjointness), but the statement quantifies over ℂ
   and only requires approximation, which is the density claim.
   The source does not say whether eigenvalues must lie inside the interval; the spectrum
   conclusion (i) already implies they do, so no separate condition is added.

9. Junk values: none. No division by zero (the uniform density uses `(2h)⁻¹` with h > 0, which is
   fine), no ℕ subtraction, no sSup of empty sets.
-/
