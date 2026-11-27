import Mathlib
/-! # Target R: definition pins (run 2026-11-27T0628Z). Mathlib's `riemannZeta` and
`DirichletCharacter.LFunction`, used by every frozen headline, are the textbook functions: away from
s = 1 each is the unique holomorphic continuation of its Dirichlet series. -/

open Complex Filter Topology

namespace TargetR.Pins

/-- Pin: Mathlib's `riemannZeta` is, away from 1, the unique holomorphic continuation of
`∑_{n ≥ 1} n^{-s}` from `re s > 1` to `ℂ \ {1}`. -/
theorem pin_riemannZeta (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f {1}ᶜ)
    (h : ∀ s : ℂ, 1 < s.re → f s = ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ s) :
    ∀ s : ℂ, s ≠ 1 → f s = riemannZeta s := by
  have hU : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hz : DifferentiableOn ℂ riemannZeta {1}ᶜ := fun s hs =>
    (differentiableAt_riemannZeta hs).differentiableWithinAt
  have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
  have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  have hev : f =ᶠ[𝓝 (2 : ℂ)] riemannZeta := by
    have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds (by norm_num : (1:ℝ) < (2:ℂ).re)] with s hs
    rw [h s hs, zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  intro s hs
  exact (hf.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq (hz.analyticOnNhd hU)
    hconn h2 hev hs

/-- Pin: Mathlib's `LFunction χ` is, away from 1, the unique holomorphic continuation of
`LSeries χ s = ∑' n, LSeries.term χ s n`, where `LSeries.term f s n = if n = 0 then 0 else f n / n ^ s`
(Mathlib's definition), i.e. `∑_{n ≥ 1} χ(n) n^{-s}`, from `re s > 1` to `ℂ \ {1}` (for every character, principal or not). -/
theorem pin_LFunction {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f {1}ᶜ)
    (h : ∀ s : ℂ, 1 < s.re → f s = LSeries (fun n : ℕ => χ n) s) :
    ∀ s : ℂ, s ≠ 1 → f s = DirichletCharacter.LFunction χ s := by
  have hU : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hz : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) {1}ᶜ := fun s hs =>
    (DirichletCharacter.differentiableAt_LFunction χ s (Or.inl hs)).differentiableWithinAt
  have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
  have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  have hev : f =ᶠ[𝓝 (2 : ℂ)] DirichletCharacter.LFunction χ := by
    have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds (by norm_num : (1:ℝ) < (2:ℂ).re)] with s hs
    rw [h s hs, DirichletCharacter.LFunction_eq_LSeries χ hs]
  intro s hs
  exact (hf.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq (hz.analyticOnNhd hU)
    hconn h2 hev hs

end TargetR.Pins
#print axioms TargetR.Pins.pin_riemannZeta
#print axioms TargetR.Pins.pin_LFunction
