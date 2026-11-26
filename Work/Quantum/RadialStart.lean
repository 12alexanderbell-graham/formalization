import Work.Quantum.FrobParam
import Mathlib.Analysis.Calculus.Deriv.Shift
/-!
# H₂⁺ route step 2, first piece: the radial solution regular at ξ = 1, with parameters (run 2026-11-26T2228Z)

Route of `runs/2026-11-26T1628Z/README.md`, step 2. The radial equation of the frozen statement
(`lean/H2PlusSigmaG.lean` of run 1628Z, with k = −2(E − 1/2)) is ((ξ² − 1) L′)′ + (4ξ − kξ² + A) L = 0. In u = ξ − 1
it is ((2u + u²) L′)′ + ((4 − k + A) + (4 − 2k) u − k u²) L = 0: `FrobParam` with w₂ = 1, v = (4 − k + A, 4 − 2k, −k).
For 0 ≤ k, A ≤ 3 the parameters are `Small`, so:
* `radial_ode`: L(ξ) = ∑ cₙ (ξ − 1)ⁿ solves the radial equation on (−1/4, 9/4) ∋ [1, 2], L(1) = 1;
* `start_continuousOn`: for any A(k) continuous on [k₁, k₂] with values in [0, 3] (the angular root of
  `AngularAssembly.angular_root`), the state (L, L′) at ξ = 2 is continuous in k — the initial value of the global
  flow (route step 2, second piece).
-/

namespace Work.Quantum.RadialStart
open Set Filter Topology
open Work.Quantum.FrobParam

/-- The radial solution regular at ξ = 1 (with L(1) = 1), in u = ξ − 1, and its u-derivative. -/
noncomputable def RL (k A u : ℝ) : ℝ := sol 1 (4 - k + A) (4 - 2 * k) (-k) u
noncomputable def RLd (k A u : ℝ) : ℝ := dsol 1 (4 - k + A) (4 - 2 * k) (-k) u

theorem small_of {k A : ℝ} (hk : k ∈ Icc (0 : ℝ) 3) (hA : A ∈ Icc (0 : ℝ) 3) :
    Small 1 (4 - k + A) (4 - 2 * k) (-k) := by
  obtain ⟨hk0, hk3⟩ := hk
  obtain ⟨hA0, hA3⟩ := hA
  refine ⟨by norm_num, abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩,
    abs_le.mpr ⟨by linarith, by linarith⟩⟩

theorem RL_one (k A : ℝ) : RL k A 0 = 1 := sol_zero _ _ _ _

/-- The radial equation in ξ on (−1/4, 9/4): L′ = Ld and ((ξ² − 1) Ld)′ = −(4ξ − kξ² + A) L. -/
theorem radial_ode {k A : ℝ} (hk : k ∈ Icc (0 : ℝ) 3) (hA : A ∈ Icc (0 : ℝ) 3) {ξ : ℝ}
    (hξ : ξ ∈ Ioo (-(1 / 4 : ℝ)) (9 / 4)) :
    HasDerivAt (fun x => RL k A (x - 1)) (RLd k A (ξ - 1)) ξ ∧
    HasDerivAt (fun x => (x ^ 2 - 1) * RLd k A (x - 1)) (-((4 * ξ - k * ξ ^ 2 + A) * RL k A (ξ - 1))) ξ := by
  have hu : ξ - 1 ∈ Ioo (-(5 / 4 : ℝ)) (5 / 4) := ⟨by linarith [hξ.1], by linarith [hξ.2]⟩
  obtain ⟨h1, h2⟩ := fc_ode (small_of hk hA) hu
  refine ⟨?_, ?_⟩
  · exact HasDerivAt.comp_sub_const ξ 1 h1
  · have := HasDerivAt.comp_sub_const ξ 1 h2
    convert this using 1
    · funext x
      simp only [RLd]
      ring
    · simp only [RL]
      ring

/-- The start state of the global radial flow at ξ = 2 (u = 1) depends continuously on k along any continuous
A(k) ∈ [0, 3]. -/
theorem start_continuousOn {k₁ k₂ : ℝ} (hk₁ : 0 ≤ k₁) (hk₂ : k₂ ≤ 3) {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc k₁ k₂)) (hR3 : ∀ k ∈ Icc k₁ k₂, R k ∈ Icc (0 : ℝ) 3) :
    ContinuousOn (fun k => RL k (R k) 1) (Icc k₁ k₂) ∧ ContinuousOn (fun k => RLd k (R k) 1) (Icc k₁ k₂) := by
  set S : Set (ℝ × ℝ) := {p | p.1 ∈ Icc (0 : ℝ) 3 ∧ p.2 ∈ Icc (0 : ℝ) 3}
  have hS : ∀ p ∈ S, Small ((fun _ : ℝ × ℝ => (1 : ℝ)) p) ((fun p : ℝ × ℝ => 4 - p.1 + p.2) p)
      ((fun p : ℝ × ℝ => 4 - 2 * p.1) p) ((fun p : ℝ × ℝ => -p.1) p) := fun p hp => small_of hp.1 hp.2
  have hs : |(1 : ℝ)| ≤ 5 / 4 := by norm_num
  have c0 := sol_continuousOn (W := fun _ : ℝ × ℝ => (1 : ℝ)) (V0 := fun p : ℝ × ℝ => 4 - p.1 + p.2)
    (V1 := fun p : ℝ × ℝ => 4 - 2 * p.1) (V2 := fun p : ℝ × ℝ => -p.1) (by fun_prop) (by fun_prop) (by fun_prop)
    (by fun_prop) hS hs
  have c1 := dsol_continuousOn (W := fun _ : ℝ × ℝ => (1 : ℝ)) (V0 := fun p : ℝ × ℝ => 4 - p.1 + p.2)
    (V1 := fun p : ℝ × ℝ => 4 - 2 * p.1) (V2 := fun p : ℝ × ℝ => -p.1) (by fun_prop) (by fun_prop) (by fun_prop)
    (by fun_prop) hS hs
  have hmap : MapsTo (fun k => (k, R k)) (Icc k₁ k₂) S := fun k hk =>
    ⟨⟨by linarith [hk.1], by linarith [hk.2]⟩, hR3 k hk⟩
  have hpair : ContinuousOn (fun k => (k, R k)) (Icc k₁ k₂) := continuousOn_id.prodMk hR
  exact ⟨c0.comp hpair hmap, c1.comp hpair hmap⟩

end Work.Quantum.RadialStart
