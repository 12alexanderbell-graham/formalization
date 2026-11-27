import Mathlib

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
