import Mathlib
import Readings.permanent
import ComparatorChallenges.PermanentCubic

/-! # Target O, family O61 (border determinantal complexity of the permanent): closures (run 2026-11-27T1628Z).

Frozen statement `OAI.PermanentBorder.permanent_cubic_lower_bounds` (challenge `PermanentCubic`, taken by name,
never retyped): for `m ≥ 1408`, every `n` with `HasBorderDeterminant n (per_m)` (respectively
`HasExactDeterminant`) has `m³ / (5 529 600 e) ≤ n`; border means `0 < n` and sequences of matrices whose
determinant polynomials converge to `per_m` coefficient by coefficient.

Links proved here:
* permanent: every reader's `per_m` is the frozen `permanentPolynomial m` (same sum, same variables).
* determinants: every reader's `det(A₀ + Σ x_j A_j)` is the frozen `affineMatrixPolynomial` (entrywise:
  `x • C a` and `x * C a` vs `C a * x`).
* border: reader C's coefficientwise limits of a sequence in the determinant set are the frozen form after choosing
  matrices; reader A's closure of coefficient vectors in the product topology, and reader B's closure in the
  topology induced from coefficient vectors, give such a sequence because the space of coefficient vectors,
  `(ι →₀ ℕ) → ℂ` with `ι` finite, is first countable (a countable product), so closure points are sequential limits.
* the readers' `c m³` with `c = 1/(5 529 600 e)` is the frozen `m³ / (5 529 600 e)`; their existential forms take
  that `c` and `m₀ = 1408`.
The family's second challenge, `SmoothInitialForm`, is a lemma-level statement from the body of the paper; no
reading of it was asked (the brief covers the introduction only). -/

namespace TargetO.Permanent

open Filter Topology MvPolynomial OAI.PermanentBorder

theorem perA (m : ℕ) : ReaderA.per m = permanentPolynomial m := rfl
theorem perB (m : ℕ) : ReaderB.per m = permanentPolynomial m := rfl
theorem perC (m : ℕ) : ReaderC.perPoly m = permanentPolynomial m := rfl

theorem detA {ι : Type*} [Fintype ι] {n : ℕ} (A₀ : Matrix (Fin n) (Fin n) ℂ) (A : ι → Matrix (Fin n) (Fin n) ℂ) :
    ReaderA.detAffine A₀ A = affineMatrixPolynomial n A₀ A := by
  unfold ReaderA.detAffine affineMatrixPolynomial
  congr 1
  ext i j
  simp [Matrix.sum_apply, mul_comm]

theorem detB {ι : Type} [Fintype ι] {n : ℕ} (A₀ : Matrix (Fin n) (Fin n) ℂ) (A : ι → Matrix (Fin n) (Fin n) ℂ) :
    (ReaderB.affineMat n A₀ A).det = affineMatrixPolynomial n A₀ A := rfl

theorem detC {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (A₀ : Matrix (Fin n) (Fin n) ℂ)
    (A : ι → Matrix (Fin n) (Fin n) ℂ) : ReaderC.detForm A₀ A = affineMatrixPolynomial n A₀ A := by
  unfold ReaderC.detForm affineMatrixPolynomial
  congr 1
  ext i j
  simp [mul_comm]

theorem const_eq (m : ℕ) : (1 / (5529600 * Real.exp 1)) * (m : ℝ) ^ 3 = (m : ℝ) ^ 3 / (5529600 * Real.exp 1) := by
  rw [one_div_mul_eq_div]

/-- From a sequence of determinant polynomials converging coefficientwise to the frozen border form. -/
theorem border_of_seq {ι : Type} [Fintype ι] (n : ℕ) (hn : 0 < n) (f : MvPolynomial ι ℂ)
    (A₀ : ℕ → Matrix (Fin n) (Fin n) ℂ) (A : ℕ → ι → Matrix (Fin n) (Fin n) ℂ)
    (h : Tendsto (fun k (d : ι →₀ ℕ) => (affineMatrixPolynomial n (A₀ k) (A k)).coeff d) atTop
      (𝓝 fun d => f.coeff d)) :
    HasBorderDeterminant n f :=
  ⟨hn, A₀, A, fun d => (continuous_apply d).continuousAt.tendsto.comp h⟩

/-- A closure point of the coefficient vectors of the frozen determinant set is a frozen border point. -/
theorem border_of_closure {ι : Type} [Fintype ι] (n : ℕ) (hn : 0 < n) (f : MvPolynomial ι ℂ)
    (h : (fun d : ι →₀ ℕ => f.coeff d) ∈ closure
      ((fun g : MvPolynomial ι ℂ => fun d : ι →₀ ℕ => g.coeff d) ''
        {g | ∃ A₀ A, g = affineMatrixPolynomial n A₀ A})) :
    HasBorderDeterminant n f := by
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 h
  choose g hg hgu using hu
  choose A₀ A hA using hg
  refine border_of_seq n hn f A₀ A ?_
  convert hlim using 1
  funext k
  rw [← hgu k, hA k]

/-! ## Reader C -/

theorem closure_C_bdc (frozen : type_of% @permanent_cubic_lower_bounds) :
    type_of% @ReaderC.reading_bdc_permanent_cubic := by
  intro m hm n ⟨hn, g, hg, hlim⟩
  choose A₀ A hA using hg
  rw [const_eq]
  refine frozen.1 m n hm ⟨hn, A₀, A, fun d => ?_⟩
  have := hlim d
  simp only [MvPolynomial.lcoeff_apply, perC] at this
  convert this using 2 with k
  rw [hA k, detC]

theorem closure_C_dc (frozen : type_of% @permanent_cubic_lower_bounds) :
    type_of% @ReaderC.reading_dc_permanent_cubic := by
  intro m hm n ⟨hn, A₀, A, hA⟩
  rw [const_eq]
  exact frozen.2 m n hm ⟨hn, A₀, A, by rw [← detC, ← perC, hA]⟩

/-! ## Reader A -/

theorem detSetA {ι : Type} [Fintype ι] (n : ℕ) :
    ReaderA.detSet ι n = {g | ∃ A₀ A, g = affineMatrixPolynomial n A₀ A} := by
  ext g; simp only [ReaderA.detSet, Set.mem_setOf_eq, detA]

theorem closure_A (frozen : type_of% @permanent_cubic_lower_bounds) :
    type_of% @ReaderA.reading_thm_1_1 := by
  intro m hm n hn h
  unfold ReaderA.InBorder at h
  rw [detSetA] at h
  have := frozen.1 m n hm (border_of_closure n hn _ h)
  unfold ReaderA.cPer; rw [const_eq]; exact this

theorem closure_A_exists (frozen : type_of% @permanent_cubic_lower_bounds) :
    type_of% @ReaderA.reading_thm_1_1_exists :=
  ⟨1 / (5529600 * Real.exp 1), by positivity, 1408, fun m hm n hn h => closure_A frozen m hm n hn h⟩

theorem closure_A_dc (frozen : type_of% @permanent_cubic_lower_bounds) : type_of% @ReaderA.reading_dc := by
  intro m hm n hn ⟨A₀, A, hA⟩
  unfold ReaderA.cPer; rw [const_eq]
  exact frozen.2 m n hm ⟨hn, A₀, A, by rw [← detA, ← perA, hA]⟩

/-! ## Reader B -/

theorem closure_B_explicit (frozen : type_of% @permanent_cubic_lower_bounds) :
    type_of% @ReaderB.readingThm1_1_explicit := by
  intro m hm n hn h
  rw [const_eq]
  refine frozen.1 m n hm (border_of_closure n hn _ ?_)
  unfold ReaderB.borderSet at h
  have hind : @Topology.IsInducing _ _ ReaderB.coeffTop _
      (fun f (d : (Fin m × Fin m) →₀ ℕ) => MvPolynomial.coeffAddMonoidHom d f) :=
    @Topology.IsInducing.mk _ _ ReaderB.coeffTop _ _ rfl
  have := hind.closure_eq_preimage_closure_image (s := ReaderB.detSet n)
  rw [this, Set.mem_preimage] at h
  have hset : (ReaderB.detSet n : Set (MvPolynomial (Fin m × Fin m) ℂ)) =
      {g | ∃ A₀ A, g = affineMatrixPolynomial n A₀ A} := by
    ext g; simp only [ReaderB.detSet, Set.mem_setOf_eq, detB]
  rw [hset] at h
  exact h

theorem closure_B_exists (frozen : type_of% @permanent_cubic_lower_bounds) :
    type_of% @ReaderB.readingThm1_1 :=
  ⟨1 / (5529600 * Real.exp 1), 1408, by positivity, fun m hm => closure_B_explicit frozen m hm⟩

theorem closure_B_dc (frozen : type_of% @permanent_cubic_lower_bounds) :
    type_of% @ReaderB.readingDC_explicit := by
  intro m hm n hn ⟨A₀, A, hA⟩
  rw [const_eq]
  exact frozen.2 m n hm ⟨hn, A₀, A, by rw [← detB, ← perB, hA]⟩

theorem reading_A1 : type_of% @ReaderA.reading_thm_1_1 := closure_A permanent_cubic_lower_bounds
theorem reading_A1e : type_of% @ReaderA.reading_thm_1_1_exists := closure_A_exists permanent_cubic_lower_bounds
theorem reading_A2 : type_of% @ReaderA.reading_dc := closure_A_dc permanent_cubic_lower_bounds
theorem reading_B1 : type_of% @ReaderB.readingThm1_1_explicit := closure_B_explicit permanent_cubic_lower_bounds
theorem reading_B1e : type_of% @ReaderB.readingThm1_1 := closure_B_exists permanent_cubic_lower_bounds
theorem reading_B2 : type_of% @ReaderB.readingDC_explicit := closure_B_dc permanent_cubic_lower_bounds
theorem reading_C1 : type_of% @ReaderC.reading_bdc_permanent_cubic := closure_C_bdc permanent_cubic_lower_bounds
theorem reading_C2 : type_of% @ReaderC.reading_dc_permanent_cubic := closure_C_dc permanent_cubic_lower_bounds

end TargetO.Permanent

#print axioms TargetO.Permanent.closure_A
#print axioms TargetO.Permanent.closure_A_exists
#print axioms TargetO.Permanent.closure_A_dc
#print axioms TargetO.Permanent.closure_B_explicit
#print axioms TargetO.Permanent.closure_B_exists
#print axioms TargetO.Permanent.closure_B_dc
#print axioms TargetO.Permanent.closure_C_bdc
#print axioms TargetO.Permanent.closure_C_dc
