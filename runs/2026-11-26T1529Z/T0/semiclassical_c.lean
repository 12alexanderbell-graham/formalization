import Mathlib

/-! Target 0(c): the algebraic step of Section 5.2 (Eqs. semi:metric-moments:a,
semi:equation-variations, semi:semiclassical-einstein) of arXiv 2611.34924, in finite dimensions.

`V` stands for metric perturbations, `W` for the values of the Einstein operator, `ι` indexes the
smeared incoming canonical variables. `E1 : V →ₗ W` is the linearized operator `E⁽¹⁾`, `E2` the
quadratic part `E⁽²⁾` (symmetric bilinear), `dg I = δ_I g`, `ddg I J = δ_I δ_J g`, `Σ` the
fluctuation two-point function. Hypothesis `hvar` is (semi:equation-variations), which the paper
derives from `E[g(φ)] = 0` on the family of solutions. Conclusion: the linearized Einstein operator
applied to the order-ħ shift `ḡ − g₀ = ½ Σ^{IJ} δ_Iδ_J g` (semi:metric-moments:a) equals
`−⟨E⁽²⁾[h,h]⟩_𝒢 = −Σ^{IJ} E⁽²⁾[δ_I g, δ_J g]`, i.e. (semi:semiclassical-einstein) at order ħ.
Not covered: the O(ħ²) remainders, smoothness of the solution map, the Bianchi identity. -/

namespace ExternalT0.Semiclassical

variable {ι V W : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

theorem one_loop_identity (E1 : V →ₗ[ℝ] W) (E2 : V →ₗ[ℝ] V →ₗ[ℝ] W)
    (dg : ι → V) (ddg : ι → ι → V) (Sg : ι → ι → ℝ)
    (hvar : ∀ I J, E1 (ddg I J) = -(2 : ℝ) • E2 (dg I) (dg J)) :
    E1 ((1 / 2 : ℝ) • ∑ I, ∑ J, Sg I J • ddg I J)
      + ∑ I, ∑ J, Sg I J • E2 (dg I) (dg J) = 0 := by
  simp only [map_smul, map_sum, hvar, Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero; intro I _
  apply Finset.sum_eq_zero; intro J _
  module

end ExternalT0.Semiclassical
#print axioms ExternalT0.Semiclassical.one_loop_identity
