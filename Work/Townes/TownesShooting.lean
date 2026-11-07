import Mathlib
import Work.Townes.TQDataA
import Work.Townes.TQDataB

/-!
# Mathematics (THE RESULT parts 5 and 2): the two shooting events that bracket the Townes
# soliton's central value (frozen before proof, run 2026-11-07T0228Z)

**Question.** The Townes soliton is the positive radial ground state Q of ΔQ − Q + Q³ = 0 in the
plane (the ground state of the two-dimensional cubic nonlinear Schrödinger equation, critical
for blow-up). Its radial profile solves
  θ'' + (1/r) θ' − θ + θ³ = 0,  θ'(0) = 0,  θ > 0,  θ(r) → 0 as r → ∞,
and the central value θ(0) is the shooting parameter. The prior-art screen of run
2026-11-07T0028Z found floating-point values only (θ(0) ≈ 2.20620086…), no rigorous enclosure.

**What is stated here.** The two shooting events, for every solution of the initial-value
problem at the singular point r = 0 (θ differentiable on [0, S] with derivative φ, φ continuous
at 0, φ' = −(1/r)φ + θ − θ³ on (0, S]), for every S ≥ 68/5:
* `townes_under`: with θ(0) = 2.2062008646, φ becomes positive at some r ≤ 68/5 while θ has
  stayed positive on [0, r] (the profile turns back up before reaching zero: undershoot);
* `townes_over`: with θ(0) = 2.2062008647, θ becomes negative at some r ≤ 68/5 while φ has
  stayed negative on (0, r] (the profile crosses zero while decreasing: overshoot).
Not yet stated: existence of a ground state with θ(0) strictly between the two values (the
open-events assembly of `Work/Math/TFExAssemble.lean`, together with global existence and the
limit θ → 0), and uniqueness (Kwong 1989; not formalised).

Only Mathlib definitions occur in the statements.
-/

namespace Work.Townes.Shooting
open Set

/-- Townes radial equation, undershoot: for every S ≥ 68/5 and every solution θ of
θ'' + (1/r)θ' − θ + θ³ = 0 on (0, S] with θ(0) = 2.2062008646, θ differentiable on [0, S] with
derivative φ and φ continuous at 0, there is r in (0, 68/5] with φ(r) > 0 and θ positive on
[0, r]. -/
theorem townes_under (S : ℝ) (hS : 68 / 5 ≤ S) (θ φ : ℝ → ℝ)
    (hθ : ∀ r ∈ Icc (0 : ℝ) S, HasDerivWithinAt θ (φ r) (Icc 0 S) r)
    (hφ0 : ContinuousWithinAt φ (Icc 0 S) 0)
    (hφ : ∀ r ∈ Ioc (0 : ℝ) S, HasDerivWithinAt φ (-(1 / r * φ r) + θ r - θ r ^ 3) (Icc 0 S) r)
    (h0 : θ 0 = 2.2062008646) :
    ∃ r ∈ Ioc (0 : ℝ) (68 / 5), 0 < φ r ∧ ∀ s ∈ Icc 0 r, 0 < θ s := by
  have hsub : Icc (0 : ℝ) (68 / 5) ⊆ Icc 0 S := Icc_subset_Icc le_rfl hS
  obtain ⟨hpos, hφe⟩ := Work.Townes.TQDataA.chain (θ := θ) (φ := φ)
    (fun s hs => (hθ s (hsub hs)).mono hsub) (hφ0.mono hsub)
    (fun s hs => (hφ s ⟨hs.1, hs.2.trans hS⟩).mono hsub) (by rw [h0]; norm_num)
  exact ⟨68 / 5, ⟨by norm_num, le_rfl⟩, hφe, hpos⟩

/-- Townes radial equation, overshoot: for every S ≥ 68/5 and every solution θ of
θ'' + (1/r)θ' − θ + θ³ = 0 on (0, S] with θ(0) = 2.2062008647, θ differentiable on [0, S] with
derivative φ and φ continuous at 0, there is r in (0, 68/5] with θ(r) < 0 and φ negative on
(0, r]. -/
theorem townes_over (S : ℝ) (hS : 68 / 5 ≤ S) (θ φ : ℝ → ℝ)
    (hθ : ∀ r ∈ Icc (0 : ℝ) S, HasDerivWithinAt θ (φ r) (Icc 0 S) r)
    (hφ0 : ContinuousWithinAt φ (Icc 0 S) 0)
    (hφ : ∀ r ∈ Ioc (0 : ℝ) S, HasDerivWithinAt φ (-(1 / r * φ r) + θ r - θ r ^ 3) (Icc 0 S) r)
    (h0 : θ 0 = 2.2062008647) :
    ∃ r ∈ Ioc (0 : ℝ) (68 / 5), θ r < 0 ∧ ∀ s ∈ Ioc 0 r, φ s < 0 := by
  have hsub : Icc (0 : ℝ) (68 / 5) ⊆ Icc 0 S := Icc_subset_Icc le_rfl hS
  obtain ⟨hneg, hθe⟩ := Work.Townes.TQDataB.chain (θ := θ) (φ := φ)
    (fun s hs => (hθ s (hsub hs)).mono hsub) (hφ0.mono hsub)
    (fun s hs => (hφ s ⟨hs.1, hs.2.trans hS⟩).mono hsub) (by rw [h0]; norm_num)
  exact ⟨68 / 5, ⟨by norm_num, le_rfl⟩, hθe, hneg⟩

end Work.Townes.Shooting
