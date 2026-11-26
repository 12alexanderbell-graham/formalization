import Mathlib

/-! Target 0: the paper's general finiteness argument for sums over intermediate states
(arXiv 2611.34924, Eqs. (bfgeo:sewing-main), (bfq:sewing-bound)): for any orthonormal (Hilbert) basis
e_α of a complex Hilbert space and unitaries U₁, U₂,
  Σ_α |⟨φ|U₂|e_α⟩⟨e_α|U₁|ψ⟩| ≤ ‖φ‖‖ψ‖,
the sum converges absolutely and equals ⟨φ|U₂U₁|ψ⟩. Certified for any countable or uncountable basis;
what it presupposes — that the paper's U are unitary on a Hilbert space with such a basis — is the
paper's construction, not checked here. -/

namespace ExternalT0.Sewing
open scoped InnerProductSpace

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem abs_sum_bound (b : HilbertBasis ι ℂ E) (x y : E) :
    Summable (fun i => ‖⟪x, b i⟫_ℂ * ⟪b i, y⟫_ℂ‖) ∧
      ∑' i, ‖⟪x, b i⟫_ℂ * ⟪b i, y⟫_ℂ‖ ≤ ‖x‖ * ‖y‖ := by
  have hp : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
  have hx := lp.hasSum_norm hp (b.repr x)
  have hy := lp.hasSum_norm hp (b.repr y)
  simp only [LinearIsometryEquiv.norm_map, ENNReal.toReal_ofNat] at hx hy
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]; norm_num
  obtain ⟨C, hC0, hC, hsum⟩ := Real.inner_le_Lp_mul_Lq_hasSum_of_nonneg hpq (norm_nonneg x)
    (norm_nonneg y) (fun i => norm_nonneg (b.repr x i)) (fun i => norm_nonneg (b.repr y i)) hx hy
  have heq : (fun i => ‖⟪x, b i⟫_ℂ * ⟪b i, y⟫_ℂ‖) = fun i => ‖b.repr x i‖ * ‖b.repr y i‖ := by
    funext i
    rw [norm_mul, b.repr_apply_apply, b.repr_apply_apply, norm_inner_symm]
  rw [heq]
  exact ⟨hsum.summable, hsum.tsum_eq ▸ hC⟩

theorem sewing (b : HilbertBasis ι ℂ E) (U₁ U₂ : E →L[ℂ] E)
    (hU₂ : ∀ v, ‖ContinuousLinearMap.adjoint U₂ v‖ = ‖v‖) (hU₁ : ∀ v, ‖U₁ v‖ = ‖v‖) (φ ψ : E) :
    HasSum (fun i => ⟪φ, U₂ (b i)⟫_ℂ * ⟪b i, U₁ ψ⟫_ℂ) ⟪φ, U₂ (U₁ ψ)⟫_ℂ ∧
      ∑' i, ‖⟪φ, U₂ (b i)⟫_ℂ * ⟪b i, U₁ ψ⟫_ℂ‖ ≤ ‖φ‖ * ‖ψ‖ := by
  have hadj : ∀ v, ⟪φ, U₂ v⟫_ℂ = ⟪ContinuousLinearMap.adjoint U₂ φ, v⟫_ℂ := fun v =>
    (ContinuousLinearMap.adjoint_inner_left U₂ v φ).symm
  simp only [hadj]
  refine ⟨b.hasSum_inner_mul_inner _ _, ?_⟩
  have h := (abs_sum_bound b (ContinuousLinearMap.adjoint U₂ φ) (U₁ ψ)).2
  rw [hU₂, hU₁] at h; exact h

end ExternalT0.Sewing
#print axioms ExternalT0.Sewing.sewing
