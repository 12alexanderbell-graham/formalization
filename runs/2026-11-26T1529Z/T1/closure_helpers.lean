import Mathlib

/-! Helpers for the target-1 closure: coordinates of derivatives on `EuclideanSpace ℝ (Fin 3)`. -/
open scoped ContDiff Laplacian
open Set

namespace ExternalT1
abbrev E := EuclideanSpace ℝ (Fin 3)
noncomputable abbrev ee (j : Fin 3) : E := EuclideanSpace.single j 1

lemma fderiv_coord {g : E → E} {x : E} (hg : DifferentiableAt ℝ g x) (i : Fin 3) (w : E) :
    fderiv ℝ (fun y => g y i) x w = (fderiv ℝ g x w) i := by
  have h := ((EuclideanSpace.proj i : E →L[ℝ] ℝ).hasFDerivAt.comp x hg.hasFDerivAt)
  rw [show (fun y => g y i) = (EuclideanSpace.proj i : E →L[ℝ] ℝ) ∘ g from rfl, h.fderiv]
  rfl

lemma vec_expand (w : E) : w = ∑ j, w j • ee j := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr w]
  simp [EuclideanSpace.basisFun_apply]

lemma clm_apply_expand (L : E →L[ℝ] E) (w : E) (i : Fin 3) :
    (L w) i = ∑ j, w j * (L (ee j)) i := by
  conv_lhs => rw [vec_expand w]
  simp [map_sum, map_smul]

lemma trace_eq (L : E →L[ℝ] E) : (L : E →ₗ[ℝ] E).trace ℝ E = ∑ i, (L (ee i)) i := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis]
  simp [Matrix.trace, LinearMap.toMatrix_apply, EuclideanSpace.basisFun_apply]

lemma gradient_coord (φ : E → ℝ) (x : E) (i : Fin 3) : gradient φ x i = fderiv ℝ φ x (ee i) := by
  have h := EuclideanSpace.inner_single_right i (1 : ℝ) (gradient φ x)
  have h' : gradient φ x i = inner ℝ (gradient φ x) (ee i) := by rw [h]; simp
  rw [h', gradient, InnerProductSpace.toDual_symm_apply]

lemma derivWithin_coord {c : ℝ → E} {t : ℝ} (ht : 0 ≤ t)
    (hc : DifferentiableWithinAt ℝ c (Ici 0) t) (i : Fin 3) :
    (derivWithin c (Ici 0) t) i = derivWithin (fun s => c s i) (Ici 0) t := by
  have h := (EuclideanSpace.proj i : E →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt t
    hc.hasDerivWithinAt
  rw [show (fun s => c s i) = (EuclideanSpace.proj i : E →L[ℝ] ℝ) ∘ c from rfl,
    h.derivWithin (uniqueDiffOn_Ici 0 t (mem_Ici.mpr ht))]
  rfl

lemma laplacian_scalar {h : E → ℝ} (hh : ContDiff ℝ 2 h) (x : E) :
    Δ h x = ∑ j, fderiv ℝ (fun y => fderiv ℝ h y (ee j)) x (ee j) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis h (EuclideanSpace.basisFun (Fin 3) ℝ)]
  apply Finset.sum_congr rfl; intro j _
  rw [iteratedFDeriv_two_apply]
  simp only [EuclideanSpace.basisFun_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hd : DifferentiableAt ℝ (fderiv ℝ h) x :=
    (hh.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

lemma laplacian_coord {g : E → E} (hg : ContDiff ℝ 2 g) (x : E) (i : Fin 3) :
    (Δ g x) i =
      ∑ j, fderiv ℝ (fun y => fderiv ℝ (fun z => g z i) y (ee j)) x (ee j) := by
  have h1 := (hg.contDiffAt (x := x)).laplacian_CLM_comp_left (l := (EuclideanSpace.proj i : E →L[ℝ] ℝ))
  have h2 : (EuclideanSpace.proj i : E →L[ℝ] ℝ) ∘ g = fun z => g z i := rfl
  rw [h2] at h1
  rw [show (Δ g x) i = (EuclideanSpace.proj i : E →L[ℝ] ℝ)
    (Δ g x) from rfl, ← Function.comp_apply (f := (EuclideanSpace.proj i : E →L[ℝ] ℝ)), ← h1]
  exact laplacian_scalar ((EuclideanSpace.proj i : E →L[ℝ] ℝ).contDiff.comp hg) x

end ExternalT1
