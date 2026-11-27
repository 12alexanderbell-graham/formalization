import Mathlib

/-!
Blind reading A of O62, "Kadison's similarity theorem through uniform derivation estimates":
Theorem 1.1 (similarity), Theorem 1.2 (uniform commutator estimate),
Corollary 1.3 (universal hyperreflexivity, with the same constant `C`).
-/

namespace ReaderA

universe u v w

open scoped InnerProductSpace

section Defs

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- `g_P(Y) = sup_{a ∈ P, ‖a‖ ≤ 1} ‖Y a - a Y‖`.
The set is nonempty (`a = 0` gives `0`) and bounded above by `2 ‖Y‖`, so `sSup` is the
true supremum (no junk value). -/
noncomputable def gP (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K) : ℝ :=
  sSup {r : ℝ | ∃ a ∈ P, ‖a‖ ≤ 1 ∧ r = ‖Y * a - a * Y‖}

/-- The Hilbert space `K^h` (ℓ²-direct sum of `h` copies of `K`). -/
abbrev Amp (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K] (h : ℕ) : Type u :=
  PiLp 2 (fun _ : Fin h => K)

/-- The natural action of an `h × h` matrix of operators on `K` on the Hilbert space `K^h`:
`(X ξ)_i = ∑_j X_{ij} ξ_j`. -/
noncomputable def matAct {h : ℕ} (X : Matrix (Fin h) (Fin h) (K →L[ℂ] K)) :
    Amp K h →L[ℂ] Amp K h where
  toFun ξ := WithLp.toLp 2 (fun i => ∑ j, X i j (WithLp.ofLp ξ j))
  map_add' ξ η := by
    ext i
    simp [Finset.sum_add_distrib]
  map_smul' c ξ := by
    ext i
    simp [Finset.smul_sum]
  cont := by
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    apply continuous_finsetSum
    intro j _
    exact (X i j).continuous.comp ((continuous_apply j).comp (PiLp.continuous_ofLp 2 _))

/-- The diagonal amplification `Y^{(h)}` of `Y` on `K^h`. -/
noncomputable def diagAmp (h : ℕ) (Y : K →L[ℂ] K) : Amp K h →L[ℂ] Amp K h :=
  matAct (Matrix.diagonal (fun _ : Fin h => Y))

/-- `X ∈ M_h(P)`: every matrix entry lies in `P`. -/
def InMatP {h : ℕ} (P : VonNeumannAlgebra K) (X : Matrix (Fin h) (Fin h) (K →L[ℂ] K)) : Prop :=
  ∀ i j, X i j ∈ P

/-- `α_M(T) = sup {‖(1 - e) T e‖ : e ∈ M', e = e* = e²}`.
Nonempty (`e = 0`) and bounded above by `‖T‖`, so `sSup` is the true supremum. -/
noncomputable def alphaM (M : VonNeumannAlgebra K) (T : K →L[ℂ] K) : ℝ :=
  sSup {r : ℝ | ∃ e ∈ M.commutant, e = star e ∧ e = e * e ∧ r = ‖(1 - e) * T * e‖}

/-- The statement of Theorem 1.2 for a given constant `C`, on Hilbert spaces in universe `u`. -/
def UniformCommutatorEstimate (C : ℝ) : Prop :=
  ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K) (h : ℕ), 1 ≤ h →
    ∀ X : Matrix (Fin h) (Fin h) (K →L[ℂ] K), InMatP P X →
      ‖diagAmp h Y * matAct X - matAct X * diagAmp h Y‖ ≤ C * gP P Y * ‖matAct X‖

/-- The statement of Corollary 1.3 with constant `2C`, on Hilbert spaces in universe `u`. -/
def UniversalHyperreflexivity (C : ℝ) : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) (T : H →L[ℂ] H),
      Metric.infDist T (M : Set (H →L[ℂ] H)) ≤ 2 * C * alphaM M T

end Defs

/-- Theorem 1.1 (Similarity). -/
theorem reading_thm_1_1_similarity
    (A : Type v) [CStarAlgebra A]
    (H : Type w) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : A →ₐ[ℂ] (H →L[ℂ] H)) (hπ : ∃ c : ℝ, ∀ a : A, ‖π a‖ ≤ c * ‖a‖) :
    ∃ S : (H →L[ℂ] H)ˣ,
      ∃ ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H), ∀ a : A, ρ a = (S : H →L[ℂ] H) * π a * ↑S⁻¹ := sorry

/-- Theorem 1.1, "in particular" form: `ρ(a*) = ρ(a)*` for `ρ(a) = S π(a) S⁻¹`. -/
theorem reading_thm_1_1_similarity_star
    (A : Type v) [CStarAlgebra A]
    (H : Type w) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : A →ₐ[ℂ] (H →L[ℂ] H)) (hπ : ∃ c : ℝ, ∀ a : A, ‖π a‖ ≤ c * ‖a‖) :
    ∃ S : (H →L[ℂ] H)ˣ, ∀ a : A,
      (S : H →L[ℂ] H) * π (star a) * ↑S⁻¹ = star ((S : H →L[ℂ] H) * π a * ↑S⁻¹) := sorry

/-- Theorem 1.2 (Uniform commutator estimate). -/
theorem reading_thm_1_2_uniform_commutator :
    ∃ C : ℝ, UniformCommutatorEstimate.{u} C := sorry

/-- Corollary 1.3 (Universal hyperreflexivity), with the same absolute constant `C`
as in Theorem 1.2. -/
theorem reading_cor_1_3_hyperreflexivity :
    ∃ C : ℝ, UniformCommutatorEstimate.{u} C ∧ UniversalHyperreflexivity.{u} C := sorry

end ReaderA

/-
AMBIGUITIES AND CHOICES

1. Unital complex C*-algebra (Thm 1.1): Mathlib's `CStarAlgebra A` (a complete normed
   ℂ-algebra with a `NormedRing`, hence a unit, star, C*-identity, star-module). The text says
   "unital"; `CStarAlgebra` is unital by construction. (If `A = 0` were allowed, everything is
   trivially fine either way.)

2. Hilbert spaces: `[NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]`, no
   separability. `B(H)` is `H →L[ℂ] H`. Universes: A in `v`, H in `w`, independent.

3. "bounded" for π: stated literally as `∃ c, ∀ a, ‖π a‖ ≤ c ‖a‖`. `π : A →ₐ[ℂ] B(H)` encodes
   complex-linear, multiplicative and unital (`π 1 = 1`).

4. "S ∈ B(H) invertible with bounded inverse": a unit `S : (H →L[ℂ] H)ˣ` (its inverse is in
   B(H), hence bounded). "ρ is a *-homomorphism": existence of a star-algebra hom
   `ρ : A →⋆ₐ[ℂ] B(H)` agreeing pointwise with `S π(·) S⁻¹`. Since `S π(·) S⁻¹` is automatically
   a unital algebra homomorphism, this is equivalent to `ρ(a*) = ρ(a)*`; the "in particular"
   clause is stated separately as `reading_thm_1_1_similarity_star`.

5. von Neumann algebras `P ⊂ B(K)`, `M ⊂ B(H)`: Mathlib's concrete `VonNeumannAlgebra K`
   (a *-subalgebra equal to its double commutant). It contains `1` of `B(K)`, which is how I
   read "unital" (unit = identity of K). The case `K = 0` is allowed, harmless.

6. g_P(Y): sSup of the set {‖Ya − aY‖ : a ∈ P, ‖a‖ ≤ 1} in ℝ. Nonempty (a = 0) and bounded
   by 2‖Y‖, so no junk sSup.

7. K^h and M_h(P): K^h is the ℓ²-sum `PiLp 2 (fun _ : Fin h => K)` (the Hilbert direct sum);
   an `h × h` matrix `X` with entries in B(K) acts by `(Xξ)_i = ∑_j X_ij ξ_j` (`matAct`).
   `X ∈ M_h(P)` means every entry is in P. `Y^{(h)}` is `matAct` of the diagonal matrix with
   all diagonal entries Y. Norms `‖[Y^{(h)},X]‖` and `‖X‖` are operator norms on B(K^h).
   The commutator `[T,U] = TU − UT` is written out explicitly.

8. "absolute constant C < ∞": `∃ C : ℝ`, chosen before all K, P, Y, h, X. Universe caveat:
   the quantification over Hilbert spaces K is over `Type u` for a fixed (universe-polymorphic)
   `u`, so formally C could depend on the universe level; this is the standard Lean
   rendering. No positivity of C is required by the text (it follows anyway for nonzero cases).

9. Corollary 1.3, "with the same C": stated as ∃ C such that both the estimate of Thm 1.2 and
   `dist(T,M) ≤ 2C α_M(T)` hold for that same C. Also `H` in the corollary ranges over
   `Type u`, same universe as Thm 1.2.

10. M' (commutant): `M.commutant` (Mathlib, = `Set.centralizer M`). Projection e: `e = e*` and
    `e = e²` written literally. α_M(T) is sSup of a set that is nonempty (e = 0) and bounded
    by ‖T‖, so not junk.

11. dist(T, M): `Metric.infDist T M` (infimum of ‖T − m‖ over m ∈ M; M nonempty, so no junk).

12. The remark "Thus every such M is hyperreflexive with constant at most 2C" is a
    restatement and not separately formalized. "No optimality" is not a claim.
-/
