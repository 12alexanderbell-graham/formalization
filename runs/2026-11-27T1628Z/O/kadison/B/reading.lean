import Mathlib

namespace ReaderB

open scoped ComplexConjugate

universe u v

/-! ### Theorem 1.1 (Similarity) -/

/-- Boundedness of an algebra homomorphism `π : A →ₐ[ℂ] B(H)`: `‖π a‖ ≤ M‖a‖` for all `a`. -/
def IsBoundedHom {A : Type u} [NormedRing A] [NormedAlgebra ℂ A] {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : A →ₐ[ℂ] (H →L[ℂ] H)) : Prop :=
  ∃ M : ℝ, ∀ a : A, ‖π a‖ ≤ M * ‖a‖

/-- Theorem 1.1.  `A →ₐ[ℂ] B(H)` is a complex-linear unital multiplicative map.  The conclusion
says: there is an invertible `S` such that `ρ a = S π(a) S⁻¹` is a `*`-homomorphism; `ρ` is
automatically a unital algebra homomorphism, so the content is `ρ(a*) = ρ(a)*`. -/
theorem readingSimilarity
    {A : Type u} [CStarAlgebra A] {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : A →ₐ[ℂ] (H →L[ℂ] H)) (hπ : IsBoundedHom π) :
    ∃ S : (H →L[ℂ] H)ˣ, ∀ a : A,
      star ((S : H →L[ℂ] H) * π a * ((S⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H)) =
        (S : H →L[ℂ] H) * π (star a) * ((S⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) := by
  sorry

/-! ### Theorem 1.2 (Uniform commutator estimate) -/

/-- `g_P(Y) = sup { ‖Y a - a Y‖ : a ∈ P, ‖a‖ ≤ 1 }`.  The set is nonempty (`a = 0`) and bounded
above by `2‖Y‖`, so `sSup` is the genuine supremum. -/
noncomputable def gP {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K) : ℝ :=
  sSup {r : ℝ | ∃ a ∈ P, ‖a‖ ≤ 1 ∧ r = ‖Y * a - a * Y‖}

/-- The Hilbert space direct sum `K^h` (`h` copies of `K`). -/
abbrev Pow2 (K : Type u) [NormedAddCommGroup K] (h : ℕ) := PiLp 2 (fun _ : Fin h => K)

/-- The operator on `K^h` given by an `h × h` matrix of operators on `K`:
`(X ξ)_i = ∑ j, X i j (ξ_j)`. -/
noncomputable def amplify {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {h : ℕ}
    (X : Matrix (Fin h) (Fin h) (K →L[ℂ] K)) : Pow2 K h →L[ℂ] Pow2 K h :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin h => K)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun i => ∑ j, (X i j) ∘L (PiLp.proj 2 (fun _ : Fin h => K) j))

/-- The diagonal amplification `Y^{(h)} = Y ⊕ ⋯ ⊕ Y` on `K^h`. -/
noncomputable def diagAmp {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (h : ℕ)
    (Y : K →L[ℂ] K) : Pow2 K h →L[ℂ] Pow2 K h :=
  amplify (Matrix.diagonal fun _ : Fin h => Y)

/-- `C` is an admissible constant for Theorem 1.2 (universe-fixed to `K : Type u`). -/
def UniformCommutatorConstant (C : ℝ) : Prop :=
  ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K) (h : ℕ), 1 ≤ h →
    ∀ X : Matrix (Fin h) (Fin h) (K →L[ℂ] K), (∀ i j, X i j ∈ P) →
      ‖diagAmp h Y * amplify X - amplify X * diagAmp h Y‖ ≤ C * gP P Y * ‖amplify X‖

/-- Theorem 1.2: an absolute constant `C` (real, hence finite). -/
theorem readingUniformCommutator : ∃ C : ℝ, UniformCommutatorConstant.{u} C := by
  sorry

/-! ### Corollary 1.3 (Universal hyperreflexivity) -/

/-- `α_M(T) = sup { ‖(1-e) T e‖ : e ∈ M', e = e* = e² }`; nonempty (`e = 0`), bounded by `‖T‖`. -/
noncomputable def alphaM {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (M : VonNeumannAlgebra H) (T : H →L[ℂ] H) : ℝ :=
  sSup {r : ℝ | ∃ e ∈ M.commutant, IsSelfAdjoint e ∧ e * e = e ∧ r = ‖(1 - e) * T * e‖}

/-- Corollary 1.3, with `C` any constant for which Theorem 1.2 holds (the "same `C`"). -/
theorem readingHyperreflexivity (C : ℝ) (hC : UniformCommutatorConstant.{u} C)
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) (T : H →L[ℂ] H) :
    Metric.infDist T (M : Set (H →L[ℂ] H)) ≤ 2 * C * alphaM M T := by
  sorry

/-
AMBIGUITIES AND CHOICES
* "Unital complex C*-algebra": `[CStarAlgebra A]` (complete, unital, C*-norm, complex normed algebra).
* "Hilbert space": complete complex inner product space; `B(H)` is `H →L[ℂ] H`.
* "bounded, complex-linear, unital algebra homomorphism": `π : A →ₐ[ℂ] B(H)` (unital by
  AlgHom), boundedness as `IsBoundedHom` (an explicit constant; M may be any real).
* "ρ is a *-homomorphism": ρ is automatically a unital algebra hom; I stated only the adjoint
  condition for ρ a = S π(a) S⁻¹ with S a unit of B(H) (bounded inverse automatic).
* g_P: sSup over a set that is nonempty and bounded above (shown by the norm bound), so no
  junk value. `P` is Mathlib's `VonNeumannAlgebra K` (unital *-subalgebra equal to its double
  commutant), so unital is built in.
* K^h is `PiLp 2` of h copies of K. M_h(P) is `Matrix (Fin h) (Fin h) (K →L[ℂ] K)` with all
  entries in P, acting by `amplify`. ‖X‖ is the operator norm of `amplify X` on K^h (the
  Matrix norm instance is deliberately not used). Y^(h) = `amplify (diagonal Y)`.
* Absolute constant C: `∃ C : ℝ`; "C < ∞" is automatic. Universe: K ranges over `Type u` for a
  fixed `u` (cannot quantify over all universes); the constant is for each fixed u. The
  corollary takes an arbitrary C valid for Theorem 1.2 at that universe (same C); it does
  not assert C ≥ 0 (follows from the hypothesis anyway, e.g. by trivial cases).
* α_M: e ranges over self-adjoint idempotents of M' = `M.commutant`.
* dist(T, M): `Metric.infDist T M`, M nonempty (contains 0), so no junk.
* No ℕ subtraction, no division, no log, no deriv, no integrals used. `h ≥ 1` stated as `1 ≤ h`.
-/

end ReaderB
