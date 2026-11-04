import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Blind specification for the Michaelis–Menten predicate `IsMMSolution`

Written without seeing the body of `IsMMSolution`, from textbook mass-action kinetics only.

Mechanism `E + S ⇌ C → E + P` with rate constants `k₁` (binding), `km₁ = k₋₁` (unbinding),
`k₂` (catalysis). Mass action gives, with `s = [S]`, `e = [E]`, `c = [C]`, `p = [P]`:

* `s' = -k₁ e s + k₋₁ c`
* `e' = -k₁ e s + (k₋₁ + k₂) c`
* `c' =  k₁ e s - (k₋₁ + k₂) c`
* `p' =  k₂ c`

on the closed interval `[0,T]` (one-sided derivatives at the endpoints, i.e.
`HasDerivWithinAt _ _ (Icc 0 T)`), with `s 0 = s₀`, `e 0 = e₀`, `c 0 = c₀`, `p 0 = p₀`.

Argument order of a candidate predicate (as in the interface):
`P k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p`.

Contents
* `refMM`         : reference definition.
* `MMSpec P`      : the spec. `law` is the DETERMINING general law; the other fields are
                    independent textbook checks (initial values, continuity, integral form,
                    conservation laws, restriction, closed-form anchors, near misses).
* `refMM_meets`   : `MMSpec refMM` (fully proved).
* `spec_pins`     : `MMSpec P → (P args ↔ refMM args)` (uses only `law`).
-/

set_option linter.dupNamespace false

namespace Checked.Fidelity.MMSpec

open Set Filter Topology Real

/-! ## Reference definition -/

/-- Reference: mass-action Michaelis–Menten kinetics on `[0,T]` with the given initial data. -/
def refMM (k₁ km₁ k₂ s₀ e₀ c₀ p₀ T : ℝ) (s e c p : ℝ → ℝ) : Prop :=
  s 0 = s₀ ∧ e 0 = e₀ ∧ c 0 = c₀ ∧ p 0 = p₀ ∧
  ∀ t ∈ Icc (0 : ℝ) T,
    HasDerivWithinAt s (-(k₁ * e t * s t) + km₁ * c t) (Icc 0 T) t ∧
    HasDerivWithinAt e (-(k₁ * e t * s t) + (km₁ + k₂) * c t) (Icc 0 T) t ∧
    HasDerivWithinAt c (k₁ * e t * s t - (km₁ + k₂) * c t) (Icc 0 T) t ∧
    HasDerivWithinAt p (k₂ * c t) (Icc 0 T) t

/-! ## The specification -/

/-- What a correct `IsMMSolution` must satisfy. -/
structure MMSpec (P : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ →
    (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → Prop) : Prop where
  /-- DETERMINING LAW: `P` holds iff the initial values match and the four mass-action rate
  equations hold on `[0,T]` (one-sided derivatives at the endpoints). -/
  law : ∀ (k₁ km₁ k₂ s₀ e₀ c₀ p₀ T : ℝ) (s e c p : ℝ → ℝ),
    P k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p ↔
      (s 0 = s₀ ∧ e 0 = e₀ ∧ c 0 = c₀ ∧ p 0 = p₀ ∧
        ∀ t ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt s (-(k₁ * e t * s t) + km₁ * c t) (Icc 0 T) t ∧
          HasDerivWithinAt e (-(k₁ * e t * s t) + (km₁ + k₂) * c t) (Icc 0 T) t ∧
          HasDerivWithinAt c (k₁ * e t * s t - (km₁ + k₂) * c t) (Icc 0 T) t ∧
          HasDerivWithinAt p (k₂ * c t) (Icc 0 T) t)
  /-- initial values -/
  init : ∀ (k₁ km₁ k₂ s₀ e₀ c₀ p₀ T : ℝ) (s e c p : ℝ → ℝ),
    P k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p → s 0 = s₀ ∧ e 0 = e₀ ∧ c 0 = c₀ ∧ p 0 = p₀
  /-- solutions are continuous on the closed interval -/
  cont : ∀ (k₁ km₁ k₂ s₀ e₀ c₀ p₀ T : ℝ) (s e c p : ℝ → ℝ),
    P k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p →
      ContinuousOn s (Icc 0 T) ∧ ContinuousOn e (Icc 0 T) ∧
      ContinuousOn c (Icc 0 T) ∧ ContinuousOn p (Icc 0 T)
  /-- integral (Volterra) form of the rate equations -/
  integral_eqs : ∀ (k₁ km₁ k₂ s₀ e₀ c₀ p₀ T : ℝ) (s e c p : ℝ → ℝ),
    P k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p → ∀ t ∈ Icc (0 : ℝ) T,
      s t = s₀ + ∫ u in (0 : ℝ)..t, (-(k₁ * e u * s u) + km₁ * c u) ∧
      e t = e₀ + ∫ u in (0 : ℝ)..t, (-(k₁ * e u * s u) + (km₁ + k₂) * c u) ∧
      c t = c₀ + ∫ u in (0 : ℝ)..t, (k₁ * e u * s u - (km₁ + k₂) * c u) ∧
      p t = p₀ + ∫ u in (0 : ℝ)..t, k₂ * c u
  /-- total enzyme `e + c` is conserved -/
  enzyme_conservation : ∀ (k₁ km₁ k₂ s₀ e₀ c₀ p₀ T : ℝ) (s e c p : ℝ → ℝ),
    P k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p → ∀ t ∈ Icc (0 : ℝ) T, e t + c t = e₀ + c₀
  /-- total substrate `s + c + p` is conserved -/
  substrate_conservation : ∀ (k₁ km₁ k₂ s₀ e₀ c₀ p₀ T : ℝ) (s e c p : ℝ → ℝ),
    P k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p → ∀ t ∈ Icc (0 : ℝ) T,
      s t + c t + p t = s₀ + c₀ + p₀
  /-- a solution on `[0,T]` is a solution on every shorter `[0,T']` -/
  restrict : ∀ (k₁ km₁ k₂ s₀ e₀ c₀ p₀ T T' : ℝ) (s e c p : ℝ → ℝ),
    P k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p → T' ≤ T → P k₁ km₁ k₂ s₀ e₀ c₀ p₀ T' s e c p
  /-- ANCHOR (no binding, `k₁ = 0`): the complex decays exponentially -/
  no_binding_c : ∀ (km₁ k₂ s₀ e₀ c₀ p₀ T : ℝ) (s e c p : ℝ → ℝ),
    P 0 km₁ k₂ s₀ e₀ c₀ p₀ T s e c p → ∀ t ∈ Icc (0 : ℝ) T,
      c t = c₀ * exp (-(km₁ + k₂) * t)
  /-- ANCHOR (no binding, `k₁ = 0`, `k₋₁ + k₂ ≠ 0`): substrate released by unbinding -/
  no_binding_s : ∀ (km₁ k₂ s₀ e₀ c₀ p₀ T : ℝ) (s e c p : ℝ → ℝ),
    km₁ + k₂ ≠ 0 → P 0 km₁ k₂ s₀ e₀ c₀ p₀ T s e c p → ∀ t ∈ Icc (0 : ℝ) T,
      s t = s₀ + km₁ * c₀ * (1 - exp (-(km₁ + k₂) * t)) / (km₁ + k₂)
  /-- ANCHOR (no binding): the explicit closed-form tuple IS a solution -/
  no_binding_sol : ∀ (km₁ k₂ s₀ e₀ c₀ p₀ T : ℝ), km₁ + k₂ ≠ 0 →
    P 0 km₁ k₂ s₀ e₀ c₀ p₀ T
      (fun t => s₀ + km₁ * c₀ * (1 - exp (-(km₁ + k₂) * t)) / (km₁ + k₂))
      (fun t => e₀ + c₀ - c₀ * exp (-(km₁ + k₂) * t))
      (fun t => c₀ * exp (-(km₁ + k₂) * t))
      (fun t => p₀ + k₂ * c₀ * (1 - exp (-(km₁ + k₂) * t)) / (km₁ + k₂))
  /-- ANCHOR (no enzyme, `e₀ = c₀ = 0`): nothing happens -/
  no_enzyme : ∀ (k₁ km₁ k₂ s₀ p₀ T : ℝ) (s e c p : ℝ → ℝ),
    P k₁ km₁ k₂ s₀ 0 0 p₀ T s e c p → ∀ t ∈ Icc (0 : ℝ) T,
      s t = s₀ ∧ e t = 0 ∧ c t = 0 ∧ p t = p₀
  /-- ANCHOR (no enzyme): the constant tuple IS a solution -/
  no_enzyme_sol : ∀ (k₁ km₁ k₂ s₀ p₀ T : ℝ),
    P k₁ km₁ k₂ s₀ 0 0 p₀ T (fun _ => s₀) (fun _ => 0) (fun _ => 0) (fun _ => p₀)
  /-- ANCHOR (no substrate, no complex): the constant tuple IS a solution -/
  no_substrate_sol : ∀ (k₁ km₁ k₂ e₀ p₀ T : ℝ),
    P k₁ km₁ k₂ 0 e₀ 0 p₀ T (fun _ => 0) (fun _ => e₀) (fun _ => 0) (fun _ => p₀)
  /-- ANCHOR (nonlinear, pure binding `k₁ = 1, k₋₁ = k₂ = 0`, `s₀ = e₀ = 1`):
  `s = e = 1/(1+t)`, `c = 1 - 1/(1+t)` -/
  binding_sol : ∀ T : ℝ,
    P 1 0 0 1 1 0 0 T (fun t => (1 + t)⁻¹) (fun t => (1 + t)⁻¹) (fun t => 1 - (1 + t)⁻¹)
      (fun _ => 0)
  /-- NEAR MISS: sign of the `k₋₁ c` term in `s'` flipped (`s' = -k₁ e s - k₋₁ c`);
  this tuple solves that wrong system with `k₁ = k₂ = 0, k₋₁ = 1, c₀ = 1`. -/
  miss_unbinding_sign :
    ¬ P 0 1 0 0 0 1 0 1 (fun t => exp (-t) - 1) (fun t => 1 - exp (-t)) (fun t => exp (-t))
      (fun _ => 0)
  /-- NEAR MISS: `p' = k₂ e s` instead of `p' = k₂ c`. -/
  miss_product_rate :
    ¬ P 0 0 1 1 1 0 0 1 (fun _ => 1) (fun _ => 1) (fun _ => 0) (fun t => t)
  /-- NEAR MISS: catalysis does not release the enzyme (`e' = -k₁ e s + k₋₁ c`). -/
  miss_enzyme_release :
    ¬ P 0 0 1 0 0 1 0 1 (fun _ => 0) (fun _ => 0) (fun t => exp (-t)) (fun t => 1 - exp (-t))
  /-- NEAR MISS: catalysis does not consume the complex (`c' = k₁ e s - k₋₁ c`). -/
  miss_complex_decay :
    ¬ P 0 0 1 0 0 1 0 1 (fun _ => 0) (fun t => t) (fun _ => 1) (fun t => t)
  /-- NEAR MISS: binding sign flipped everywhere (`s' = e' = +k₁ e s`, `c' = -k₁ e s`); this
  tuple solves that wrong system and satisfies both conservation laws. -/
  miss_binding_sign :
    ¬ P 1 0 0 1 1 0 0 (1 / 2) (fun t => (1 - t)⁻¹) (fun t => (1 - t)⁻¹)
      (fun t => 1 - (1 - t)⁻¹) (fun _ => 0)
  /-- NEAR MISS: wrong initial value (a steady state, but not starting at `s₀ = 0`). -/
  miss_init : ¬ P 1 1 1 0 0 0 0 1 (fun _ => 1) (fun _ => 0) (fun _ => 0) (fun _ => 0)
  /-- NEAR MISS: correct except for a jump at the right endpoint `t = T`. -/
  miss_endpoint :
    ¬ P 1 1 1 1 0 0 0 1 (fun t => if t = 1 then 2 else 1) (fun _ => 0) (fun _ => 0) (fun _ => 0)

/-! ## The spec pins the predicate -/

theorem spec_pins {P : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ →
    (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → Prop} (h : MMSpec P) :
    ∀ (k₁ km₁ k₂ s₀ e₀ c₀ p₀ T : ℝ) (s e c p : ℝ → ℝ),
      P k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p ↔ refMM k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p :=
  fun k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p => h.law k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p

/-! ## Analytic helpers -/

lemma mem_nhdsGE_Icc {T s : ℝ} (hs : s ∈ Ico (0 : ℝ) T) : Icc (0 : ℝ) T ∈ 𝓝[≥] s :=
  mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc_left hs.1)

/-- zero one-sided derivative on `[0,T]` ⇒ constant. -/
lemma const_of_deriv_zero {T : ℝ} {g : ℝ → ℝ}
    (hg : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt g 0 (Icc 0 T) t) :
    ∀ t ∈ Icc (0 : ℝ) T, g t = g 0 :=
  constant_of_has_deriv_right_zero (fun t ht => (hg t ht).continuousWithinAt)
    (fun s hs => (hg s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin (mem_nhdsGE_Icc hs))

/-- Gronwall: `x' = a x` with `a` bounded and `x 0 = 0` ⇒ `x = 0` on `[0,T]`. -/
lemma zero_of_linear {T A : ℝ} {x a : ℝ → ℝ}
    (hx : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt x (a t * x t) (Icc 0 T) t)
    (ha : ∀ t ∈ Icc (0 : ℝ) T, |a t| ≤ A) (h0 : x 0 = 0) :
    ∀ t ∈ Icc (0 : ℝ) T, x t = 0 := by
  intro t ht
  have key := norm_le_gronwallBound_of_norm_deriv_right_le (f := x)
    (f' := fun s => a s * x s) (δ := 0) (K := A) (ε := 0)
    (fun s hs => (hx s hs).continuousWithinAt)
    (fun s hs => (hx s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin (mem_nhdsGE_Icc hs))
    (by simp [h0])
    (fun s hs => by
      rw [add_zero, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (ha s (Ico_subset_Icc_self hs)) (abs_nonneg _))
    t ht
  rw [gronwallBound_ε0_δ0] at key
  exact norm_eq_zero.mp (le_antisymm key (norm_nonneg _))

/-- FTC on `[0,T]` for one-sided derivatives with continuous derivative. -/
lemma integral_of_deriv {T : ℝ} {f g : ℝ → ℝ}
    (hf : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt f (g t) (Icc 0 T) t)
    (hg : ContinuousOn g (Icc 0 T)) :
    ∀ t ∈ Icc (0 : ℝ) T, f t = f 0 + ∫ u in (0 : ℝ)..t, g u := by
  intro t ht
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have hfc : ContinuousOn f (Icc 0 T) := fun x hx => (hf x hx).continuousWithinAt
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1 (hfc.mono hsub)
    (fun x hx => ((hf x ((Ioo_subset_Icc_self.trans hsub) hx)).hasDerivAt
        (Icc_mem_nhds hx.1 (lt_of_lt_of_le hx.2 ht.2))).hasDerivWithinAt)
    ((hg.mono (by rw [uIcc_of_le ht.1]; exact hsub)).intervalIntegrable)
  linarith

/-- Build `refMM` from (two-sided) derivatives at the points of `[0,T]`. -/
lemma refMM_of_hasDerivAt {k₁ km₁ k₂ s₀ e₀ c₀ p₀ T : ℝ} {s e c p : ℝ → ℝ}
    (hs0 : s 0 = s₀) (he0 : e 0 = e₀) (hc0 : c 0 = c₀) (hp0 : p 0 = p₀)
    (hs : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt s (-(k₁ * e t * s t) + km₁ * c t) t)
    (he : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt e (-(k₁ * e t * s t) + (km₁ + k₂) * c t) t)
    (hc : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt c (k₁ * e t * s t - (km₁ + k₂) * c t) t)
    (hp : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt p (k₂ * c t) t) :
    refMM k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p :=
  ⟨hs0, he0, hc0, hp0, fun t ht => ⟨(hs t ht).hasDerivWithinAt, (he t ht).hasDerivWithinAt,
    (hc t ht).hasDerivWithinAt, (hp t ht).hasDerivWithinAt⟩⟩

lemma hasDerivAt_expLin (κ t : ℝ) :
    HasDerivAt (fun t => exp (-κ * t)) (-κ * exp (-κ * t)) t := by
  have := ((hasDerivAt_id' t).const_mul (-κ)).exp
  convert this using 1
  ring

/-! ## Properties of the reference -/

section ref

variable {k₁ km₁ k₂ s₀ e₀ c₀ p₀ T : ℝ} {s e c p : ℝ → ℝ}

lemma refMM_cont (h : refMM k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p) :
    ContinuousOn s (Icc 0 T) ∧ ContinuousOn e (Icc 0 T) ∧
      ContinuousOn c (Icc 0 T) ∧ ContinuousOn p (Icc 0 T) :=
  ⟨fun t ht => (h.2.2.2.2 t ht).1.continuousWithinAt,
   fun t ht => (h.2.2.2.2 t ht).2.1.continuousWithinAt,
   fun t ht => (h.2.2.2.2 t ht).2.2.1.continuousWithinAt,
   fun t ht => (h.2.2.2.2 t ht).2.2.2.continuousWithinAt⟩

lemma refMM_enzyme (h : refMM k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p) :
    ∀ t ∈ Icc (0 : ℝ) T, e t + c t = e₀ + c₀ := by
  obtain ⟨-, he0, hc0, -, hd⟩ := h
  intro t ht
  have := const_of_deriv_zero (g := fun t => e t + c t)
    (fun t ht => ((hd t ht).2.1.add (hd t ht).2.2.1).congr_deriv (by ring)) t ht
  simpa [he0, hc0] using this

lemma refMM_mass (h : refMM k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p) :
    ∀ t ∈ Icc (0 : ℝ) T, s t + c t + p t = s₀ + c₀ + p₀ := by
  obtain ⟨hs0, -, hc0, hp0, hd⟩ := h
  intro t ht
  have := const_of_deriv_zero (g := fun t => s t + c t + p t)
    (fun t ht => (((hd t ht).1.add (hd t ht).2.2.1).add (hd t ht).2.2.2).congr_deriv
      (by ring)) t ht
  simpa [hs0, hc0, hp0] using this

lemma refMM_integral (h : refMM k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p) :
    ∀ t ∈ Icc (0 : ℝ) T,
      s t = s₀ + ∫ u in (0 : ℝ)..t, (-(k₁ * e u * s u) + km₁ * c u) ∧
      e t = e₀ + ∫ u in (0 : ℝ)..t, (-(k₁ * e u * s u) + (km₁ + k₂) * c u) ∧
      c t = c₀ + ∫ u in (0 : ℝ)..t, (k₁ * e u * s u - (km₁ + k₂) * c u) ∧
      p t = p₀ + ∫ u in (0 : ℝ)..t, k₂ * c u := by
  obtain ⟨cs, ce, cc, -⟩ := refMM_cont h
  obtain ⟨hs0, he0, hc0, hp0, hd⟩ := h
  intro t ht
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hs0]; exact integral_of_deriv (fun t ht => (hd t ht).1) (by fun_prop) t ht
  · rw [← he0]; exact integral_of_deriv (fun t ht => (hd t ht).2.1) (by fun_prop) t ht
  · rw [← hc0]; exact integral_of_deriv (fun t ht => (hd t ht).2.2.1) (by fun_prop) t ht
  · rw [← hp0]; exact integral_of_deriv (fun t ht => (hd t ht).2.2.2) (by fun_prop) t ht

lemma refMM_restrict {T' : ℝ} (h : refMM k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p) (hT : T' ≤ T) :
    refMM k₁ km₁ k₂ s₀ e₀ c₀ p₀ T' s e c p := by
  obtain ⟨hs0, he0, hc0, hp0, hd⟩ := h
  have hsub : Icc (0 : ℝ) T' ⊆ Icc 0 T := Icc_subset_Icc_right hT
  exact ⟨hs0, he0, hc0, hp0, fun t ht =>
    ⟨(hd t (hsub ht)).1.mono hsub, (hd t (hsub ht)).2.1.mono hsub,
     (hd t (hsub ht)).2.2.1.mono hsub, (hd t (hsub ht)).2.2.2.mono hsub⟩⟩

lemma refMM_no_binding_c (h : refMM 0 km₁ k₂ s₀ e₀ c₀ p₀ T s e c p) :
    ∀ t ∈ Icc (0 : ℝ) T, c t = c₀ * exp (-(km₁ + k₂) * t) := by
  obtain ⟨-, -, hc0, -, hd⟩ := h
  intro t ht
  have := zero_of_linear (T := T) (A := |km₁ + k₂|)
    (x := fun t => c t - c₀ * exp (-(km₁ + k₂) * t)) (a := fun _ => -(km₁ + k₂))
    (fun t ht => ((hd t ht).2.2.1.sub
      ((hasDerivAt_expLin (km₁ + k₂) t).const_mul c₀).hasDerivWithinAt).congr_deriv
        (by ring))
    (fun t _ => (abs_neg _).le) (by simp [hc0]) t ht
  linarith

lemma refMM_no_binding_s (hκ : km₁ + k₂ ≠ 0) (h : refMM 0 km₁ k₂ s₀ e₀ c₀ p₀ T s e c p) :
    ∀ t ∈ Icc (0 : ℝ) T, s t = s₀ + km₁ * c₀ * (1 - exp (-(km₁ + k₂) * t)) / (km₁ + k₂) := by
  have hc := refMM_no_binding_c h
  obtain ⟨hs0, -, -, -, hd⟩ := h
  intro t ht
  have := const_of_deriv_zero (T := T)
    (g := fun t => s t - (s₀ + km₁ * c₀ * (1 - exp (-(km₁ + k₂) * t)) / (km₁ + k₂)))
    (fun t ht => ((hd t ht).1.sub (((((hasDerivAt_expLin (km₁ + k₂) t).const_sub 1).const_mul
      (km₁ * c₀)).div_const (km₁ + k₂)).const_add s₀).hasDerivWithinAt).congr_deriv (by
        rw [hc t ht]; field_simp; ring)) t ht
  simp only [mul_zero, Real.exp_zero, sub_self, zero_div, add_zero, hs0] at this
  linarith

lemma refMM_no_enzyme (h : refMM k₁ km₁ k₂ s₀ 0 0 p₀ T s e c p) :
    ∀ t ∈ Icc (0 : ℝ) T, s t = s₀ ∧ e t = 0 ∧ c t = 0 ∧ p t = p₀ := by
  have hcons := refMM_enzyme h
  obtain ⟨cs, -, -, -⟩ := refMM_cont h
  obtain ⟨hs0, -, hc0, hp0, hd⟩ := h
  have hq : ContinuousOn (fun t => -(k₁ * s t) - (km₁ + k₂)) (Icc 0 T) := by fun_prop
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn hq
  have hee : ∀ t ∈ Icc (0 : ℝ) T, e t = -c t := fun t ht => by linarith [hcons t ht]
  have hc : ∀ t ∈ Icc (0 : ℝ) T, c t = 0 := zero_of_linear (A := A)
    (a := fun t => -(k₁ * s t) - (km₁ + k₂))
    (fun t ht => (hd t ht).2.2.1.congr_deriv (by rw [hee t ht]; ring))
    (fun t ht => by simpa [Real.norm_eq_abs] using hA t ht) hc0
  have he : ∀ t ∈ Icc (0 : ℝ) T, e t = 0 := fun t ht => by rw [hee t ht, hc t ht, neg_zero]
  intro t ht
  refine ⟨?_, he t ht, hc t ht, ?_⟩
  · rw [← hs0]
    exact const_of_deriv_zero (fun t ht => (hd t ht).1.congr_deriv
      (by rw [he t ht, hc t ht]; ring)) t ht
  · rw [← hp0]
    exact const_of_deriv_zero (fun t ht => (hd t ht).2.2.2.congr_deriv
      (by rw [hc t ht]; ring)) t ht

end ref

lemma exp_neg_one_lt_one : exp (-1 : ℝ) < 1 := by simp

/-! ## The reference meets the spec -/

theorem refMM_meets : MMSpec refMM where
  law := fun _ _ _ _ _ _ _ _ _ _ _ _ => Iff.rfl
  init := fun _ _ _ _ _ _ _ _ _ _ _ _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  cont := fun _ _ _ _ _ _ _ _ _ _ _ _ h => refMM_cont h
  integral_eqs := fun _ _ _ _ _ _ _ _ _ _ _ _ h => refMM_integral h
  enzyme_conservation := fun _ _ _ _ _ _ _ _ _ _ _ _ h => refMM_enzyme h
  substrate_conservation := fun _ _ _ _ _ _ _ _ _ _ _ _ h => refMM_mass h
  restrict := fun _ _ _ _ _ _ _ _ _ _ _ _ _ h hT => refMM_restrict h hT
  no_binding_c := fun _ _ _ _ _ _ _ _ _ _ _ h => refMM_no_binding_c h
  no_binding_s := fun _ _ _ _ _ _ _ _ _ _ _ hκ h => refMM_no_binding_s hκ h
  no_binding_sol := by
    intro km₁ k₂ s₀ e₀ c₀ p₀ T hκ
    have hE := hasDerivAt_expLin (km₁ + k₂)
    refine refMM_of_hasDerivAt (by simp) (by simp) (by simp) (by simp)
      (fun t _ => ?_) (fun t _ => ?_) (fun t _ => ?_) (fun t _ => ?_)
    · convert ((((hE t).const_sub 1).const_mul (km₁ * c₀)).div_const (km₁ + k₂)).const_add s₀
        using 1
      field_simp
      ring
    · convert ((hE t).const_mul c₀).const_sub (e₀ + c₀) using 1
      ring
    · convert (hE t).const_mul c₀ using 1
      ring
    · convert ((((hE t).const_sub 1).const_mul (k₂ * c₀)).div_const (km₁ + k₂)).const_add p₀
        using 1
      field_simp
  no_enzyme := fun _ _ _ _ _ _ _ _ _ _ h => refMM_no_enzyme h
  no_enzyme_sol := by
    intro k₁ km₁ k₂ s₀ p₀ T
    refine refMM_of_hasDerivAt rfl rfl rfl rfl (fun t _ => ?_) (fun t _ => ?_)
      (fun t _ => ?_) (fun t _ => ?_) <;>
    simpa using hasDerivAt_const t _
  no_substrate_sol := by
    intro k₁ km₁ k₂ e₀ p₀ T
    refine refMM_of_hasDerivAt rfl rfl rfl rfl (fun t _ => ?_) (fun t _ => ?_)
      (fun t _ => ?_) (fun t _ => ?_) <;>
    simpa using hasDerivAt_const t _
  binding_sol := by
    intro T
    have hd : ∀ t ∈ Icc (0 : ℝ) T,
        HasDerivAt (fun t => (1 + t)⁻¹) (-1 / (1 + t) ^ 2) t := fun t ht => by
      have h1 : (1 : ℝ) + t ≠ 0 := by linarith [ht.1]
      exact ((hasDerivAt_id' t).const_add 1).inv h1
    refine refMM_of_hasDerivAt (by norm_num) (by norm_num) (by norm_num) rfl
      (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_) (fun t _ => ?_)
    · have h1 : (1 : ℝ) + t ≠ 0 := by linarith [ht.1]
      convert hd t ht using 1
      field_simp
      ring
    · have h1 : (1 : ℝ) + t ≠ 0 := by linarith [ht.1]
      convert hd t ht using 1
      field_simp
      ring
    · have h1 : (1 : ℝ) + t ≠ 0 := by linarith [ht.1]
      convert (hd t ht).const_sub 1 using 1
      field_simp
      ring
    · simpa using hasDerivAt_const t (0 : ℝ)
  miss_unbinding_sign := by
    intro h
    have := refMM_mass h 1 ⟨zero_le_one, le_rfl⟩
    linarith [exp_neg_one_lt_one]
  miss_product_rate := by
    intro h
    have := refMM_mass h 1 ⟨zero_le_one, le_rfl⟩
    norm_num at this
  miss_enzyme_release := by
    intro h
    have := refMM_enzyme h 1 ⟨zero_le_one, le_rfl⟩
    linarith [exp_neg_one_lt_one]
  miss_complex_decay := by
    intro h
    have := refMM_enzyme h 1 ⟨zero_le_one, le_rfl⟩
    norm_num at this
  miss_binding_sign := by
    intro h
    have h1 := (h.2.2.2.2 0 ⟨le_rfl, by norm_num⟩).1
    have h2 : HasDerivAt (fun t : ℝ => (1 - t)⁻¹) (-(-1) / (1 - 0) ^ 2) 0 :=
      ((hasDerivAt_id' (0 : ℝ)).const_sub 1).inv (by norm_num)
    have := UniqueDiffWithinAt.eq_deriv _
      (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1 / 2) 0 ⟨le_rfl, by norm_num⟩)
      h1 h2.hasDerivWithinAt
    norm_num at this
  miss_init := by
    intro h
    exact one_ne_zero h.1
  miss_endpoint := by
    intro h
    have := (refMM_no_enzyme h 1 ⟨zero_le_one, le_rfl⟩).1
    norm_num at this

/-! ## Sanity checks: the near-miss tuples DO solve the corresponding wrong systems -/

/-- Wrong system: binding sign flipped. -/
def wrongBindingMM (k₁ km₁ k₂ s₀ e₀ c₀ p₀ T : ℝ) (s e c p : ℝ → ℝ) : Prop :=
  s 0 = s₀ ∧ e 0 = e₀ ∧ c 0 = c₀ ∧ p 0 = p₀ ∧
  ∀ t ∈ Icc (0 : ℝ) T,
    HasDerivWithinAt s (k₁ * e t * s t + km₁ * c t) (Icc 0 T) t ∧
    HasDerivWithinAt e (k₁ * e t * s t + (km₁ + k₂) * c t) (Icc 0 T) t ∧
    HasDerivWithinAt c (-(k₁ * e t * s t) - (km₁ + k₂) * c t) (Icc 0 T) t ∧
    HasDerivWithinAt p (k₂ * c t) (Icc 0 T) t

example : wrongBindingMM 1 0 0 1 1 0 0 (1 / 2) (fun t => (1 - t)⁻¹) (fun t => (1 - t)⁻¹)
    (fun t => 1 - (1 - t)⁻¹) (fun _ => 0) := by
  have hd : ∀ t ∈ Icc (0 : ℝ) (1 / 2),
      HasDerivAt (fun t : ℝ => (1 - t)⁻¹) (-(-1) / (1 - t) ^ 2) t := fun t ht => by
    have h1 : (1 : ℝ) - t ≠ 0 := by linarith [ht.2]
    exact ((hasDerivAt_id' t).const_sub 1).inv h1
  refine ⟨by norm_num, by norm_num, by norm_num, rfl, fun t ht => ⟨?_, ?_, ?_, ?_⟩⟩
  · have h1 : (1 : ℝ) - t ≠ 0 := by linarith [ht.2]
    convert (hd t ht).hasDerivWithinAt using 1
    field_simp
    ring
  · have h1 : (1 : ℝ) - t ≠ 0 := by linarith [ht.2]
    convert (hd t ht).hasDerivWithinAt using 1
    field_simp
    ring
  · have h1 : (1 : ℝ) - t ≠ 0 := by linarith [ht.2]
    convert ((hd t ht).const_sub 1).hasDerivWithinAt using 1
    field_simp
    ring
  · simpa using hasDerivWithinAt_const t (Icc (0 : ℝ) (1 / 2)) (0 : ℝ)

end Checked.Fidelity.MMSpec
