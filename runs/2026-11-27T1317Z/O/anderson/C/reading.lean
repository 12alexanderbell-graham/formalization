import Mathlib

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
