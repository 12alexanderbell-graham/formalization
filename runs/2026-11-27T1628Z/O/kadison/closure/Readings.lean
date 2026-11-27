import Mathlib

/-! # Target O, family kadison: the three blind readings of run 2026-11-27T1628Z (brief 5b216ff), concatenated unchanged
apart from the repeated `import Mathlib` lines, so a closure can import them as one module. -/


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


/-!
Blind reading C, target O, family O62: Kadison's similarity theorem through uniform
derivation estimates. Definitions are written from the source excerpt; the claims are
`sorry`. See the comment block at the end for ambiguities and choices.
-/

namespace ReaderC

universe u

/-- A unital von Neumann algebra P in B(K), by the bicommutant characterisation:
P is a unital *-subalgebra (`StarSubalgebra`) with 1 in P and P'' = P. -/
def IsUnitalVN {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (P : StarSubalgebra ℂ (K →L[ℂ] K)) : Prop :=
  (1 : K →L[ℂ] K) ∈ P ∧
    Set.centralizer (Set.centralizer (P : Set (K →L[ℂ] K))) = (P : Set (K →L[ℂ] K))

/-- Euclidean (ℓ²) norm on K^h, the Hilbert direct sum, written out by hand. -/
noncomputable def l2norm {K : Type u} [NormedAddCommGroup K] {h : ℕ} (x : Fin h → K) : ℝ :=
  Real.sqrt (∑ i, ‖x i‖ ^ 2)

/-- Operator norm of a map T on K^h: supremum of ‖T x‖ over the ℓ² unit ball. -/
noncomputable def opNormH {K : Type u} [NormedAddCommGroup K] {h : ℕ}
    (T : (Fin h → K) → (Fin h → K)) : ℝ :=
  sSup ((fun x => l2norm (T x)) '' {x : Fin h → K | l2norm x ≤ 1})

/-- The action of X ∈ M_h(B(K)) on K^h: (X x)_i = ∑_j X_{ij} x_j. -/
def matAct {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {h : ℕ}
    (X : Matrix (Fin h) (Fin h) (K →L[ℂ] K)) (x : Fin h → K) : Fin h → K :=
  fun i => ∑ j, X i j (x j)

/-- Diagonal amplification Y^(h) of Y ∈ B(K) on K^h: (Y^(h) x)_i = Y x_i. -/
def diagAmp {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {h : ℕ}
    (Y : K →L[ℂ] K) (x : Fin h → K) : Fin h → K :=
  fun i => Y (x i)

/-- g_P(Y) = sup over a ∈ P with ‖a‖ ≤ 1 of ‖Y a − a Y‖. -/
noncomputable def gP {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (P : StarSubalgebra ℂ (K →L[ℂ] K)) (Y : K →L[ℂ] K) : ℝ :=
  sSup ((fun a : K →L[ℂ] K => ‖Y * a - a * Y‖) '' {a : K →L[ℂ] K | a ∈ P ∧ ‖a‖ ≤ 1})

/-- The property "C is an absolute constant for Theorem 1.2": for every complex Hilbert space K,
every unital von Neumann algebra P in B(K), every Y in B(K), every h ≥ 1 and every X in M_h(P),
‖[Y^(h), X]‖ ≤ C g_P(Y) ‖X‖, where [Y^(h), X] x = Y^(h)(X x) − X(Y^(h) x). -/
def UniformCommutatorConst (C : ℝ) : Prop :=
  ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (P : StarSubalgebra ℂ (K →L[ℂ] K)), IsUnitalVN P →
    ∀ (Y : K →L[ℂ] K) (h : ℕ), 1 ≤ h →
    ∀ X : Matrix (Fin h) (Fin h) (K →L[ℂ] K), (∀ i j, X i j ∈ P) →
      opNormH (fun x => diagAmp Y (matAct X x) - matAct X (diagAmp Y x)) ≤
        C * gP P Y * opNormH (matAct X)

/-- Theorem 1.1 (similarity). -/
theorem reading_thm_1_1 :
    ∀ (A : Type u) [CStarAlgebra A] (H : Type u) [NormedAddCommGroup H]
      [InnerProductSpace ℂ H] [CompleteSpace H] (π : A →ₐ[ℂ] (H →L[ℂ] H)),
      (∃ M : ℝ, ∀ a : A, ‖π a‖ ≤ M * ‖a‖) →
      ∃ S T : H →L[ℂ] H, S * T = 1 ∧ T * S = 1 ∧
        ∃ ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H),
          (∀ a : A, ρ a = S * π a * T) ∧ ∀ a : A, ρ (star a) = star (ρ a) :=
  sorry

/-- Theorem 1.2 (uniform commutator estimate): there is an absolute constant C < ∞. -/
theorem reading_thm_1_2 : ∃ C : ℝ, UniformCommutatorConst C :=
  sorry

/-- α_M(T) = sup { ‖(1 − e) T e‖ : e ∈ M', e = e* = e² }. -/
noncomputable def alphaM {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (M : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H) : ℝ :=
  sSup ((fun e : H →L[ℂ] H => ‖(1 - e) * T * e‖) ''
    {e : H →L[ℂ] H | e ∈ Set.centralizer (M : Set (H →L[ℂ] H)) ∧ star e = e ∧ e * e = e})

/-- Corollary 1.3 (universal hyperreflexivity), with C any constant as in Theorem 1.2. -/
theorem reading_cor_1_3 (C : ℝ) (hC : UniformCommutatorConst C) :
    ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (M : StarSubalgebra ℂ (H →L[ℂ] H)), IsUnitalVN M → ∀ T : H →L[ℂ] H,
      Metric.infDist T (M : Set (H →L[ℂ] H)) ≤ 2 * C * alphaM M T :=
  sorry

end ReaderC

/-!
## Comment block: ambiguities and choices (reader C, O62)

1. Hilbert spaces: "complex Hilbert space" is a complete inner product space over ℂ
   (`InnerProductSpace ℂ`, `CompleteSpace`). Algebras are B(H) = `H →L[ℂ] H`, with Mathlib's
   operator norm and adjoint (`star`).

2. Theorem 1.1. "Bounded" for π: taken as ∃ M : ℝ with ‖π a‖ ≤ M‖a‖ for all a. "Complex-linear
   unital algebra homomorphism" is `A →ₐ[ℂ] B(H)` (AlgHom preserves 1 by definition). "Invertible
   with bounded inverse" is: ∃ S, T in B(H) with S T = 1 = T S (so T = S⁻¹ is bounded). ρ is a
   *-homomorphism, formalised as `A →⋆ₐ[ℂ] B(H)`; the "in particular" clause is restated as an
   explicit conjunct although it follows from the StarAlgHom structure. The domain A is a
   `CStarAlgebra` (unital, Mathlib's class), so the unit is included.

3. Universes: K, H, A are all in one universe `u`; the statements quantify over all types in
   that universe, which is the only way to write "every Hilbert space" in a single theorem.

4. Unital von Neumann algebra: the text does not define it. I used the bicommutant form: a unital
   *-subalgebra P (StarSubalgebra, so *-closed) with 1 ∈ P and P'' = P. Von Neumann's bicommutant
   theorem says this equals WOT-closedness, so this is a faithful encoding. Commutant M' is
   `Set.centralizer`, i.e. {c | ∀ m ∈ M, m c = c m}.

5. Amplifications. K^h is given the ℓ² (Hilbert direct sum) norm, written out by hand as
   sqrt(∑ ‖x_i‖²) on `Fin h → K` (not Mathlib's PiLp, to avoid version-dependent WithLp API).
   This is exactly the Hilbert norm on K^h. M_h(P) acts by matrix multiplication, (Xx)_i = ∑_j X_ij x_j,
   and Y^(h) is the diagonal (Y^(h) x)_i = Y x_i. Operator norms of maps on K^h are suprema over the
   ℓ²-unit ball (`opNormH`). The commutator is [Y^(h), X] = Y^(h)X − XY^(h) acting on K^h, and
   ‖X‖ in the estimate is the operator norm of X on K^h, as the text states ‖X‖ for X ∈ M_h(P).

6. Junk values. `sSup` in ℝ is 0 on the empty or unbounded-above set, so I check the sets are
   fine: in `gP` the set is nonempty (a = 0 ∈ P, value 0) and bounded (‖Ya − aY‖ ≤ 2‖Y‖);
   in `alphaM` the set is nonempty (e = 0 is in M' and is a projection) and bounded by 2‖T‖
   (projections have norm ≤ 1); in `opNormH` the set is nonempty (x = 0) and bounded because the
   maps in question are bounded linear maps (for matAct X, ‖Xx‖ ≤ (∑‖X_ij‖)‖x‖; the commutator is
   a difference of bounded maps). So no junk value is used for the claimed inequalities, although
   the definitions themselves are only faithful on these bounded sets.

7. The constant C. "There is an absolute constant C<∞" is `∃ C : ℝ`. I did not add C > 0, since the
   text does not state positivity; a negative C would make the inequality false whenever the right
   side is nonzero, so the claim itself already forces the sign. Theorem 1.2 quantifies the
   universe-level `∀ K` *inside* the ∃ C, which is the literal reading of "absolute constant".

8. Theorem 1.2's C is expressed through `UniformCommutatorConst C`, a `def` that is a verbatim
   transcription of the displayed estimate (the bound is ‖[Y^(h),X]‖ ≤ C g_P(Y)‖X‖).

9. Corollary 1.3. The hypothesis hC says C is a constant as in Theorem 1.2, matching "with the
   absolute constant C from Theorem 1.1" (the text's label is thm:universal). dist(T, M) is
   Mathlib's `Metric.infDist` (inf of ‖T − S‖ over S in M). The corollary's "hyperreflexive with
   constant at most 2C" is the same inequality with the constant 2C, so it is not stated separately.
   α_M is defined with sup over projections e in M' as the text does. No optimality is claimed.

10. Not formalised: the text's remark on the history and the proof strategy (omitted lines 33–94).
    No Mathlib notion was missing; everything above is defined here from the excerpt.
-/
