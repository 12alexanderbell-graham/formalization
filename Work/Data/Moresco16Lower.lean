import Mathlib
import Work.Data.Moresco16

/-!
# Toward a certified lower bound of the open-ΛCDM χ² of Moresco et al. 2016 Table 4

Generic tools (run 2026-11-05T0428Z) for proving c ≤ `chiSqOL H₀ Ω_m Ω_Λ` for every H₀ and every
(Ω_m, Ω_Λ) in a box at which all thirty E² are nonnegative:

* `chiSqOL_eq`: with y_i = E²(z_i) ≥ 0, χ² = α H₀² − 2 β H₀ + γ, α = Σ y_i/σ_i² + 1/2.4²,
  β = Σ H_i √y_i/σ_i² + 73/2.4², γ = Σ H_i²/σ_i² + 73²/2.4² (α, γ affine/constant in the
  parameters; only β carries square roots).
* `ge_of_disc`: α > 0 and β² ≤ α (γ − c) give c ≤ α H₀² − 2 β H₀ + γ for every H₀.
* `sqrt_le_tangent`: √y ≤ (y + s²)/(2s) for y ≥ 0, s > 0, so β ≤ L with L affine in the
  parameters (one rational s_i per box and redshift).
* `box_convex`: (p + q m + r l)² ≤ a + b m + d l at the four corners of a box implies it on the
  whole box (the left side minus the right is convex).

Feasibility (float, `runs/2026-11-05T0428Z/scripts/feas_m16_lower.py`): c = 14.6 over
Ω_m ∈ [0, 1], Ω_Λ ∈ [0, 8] needs 267 boxes (a box on which some y_i is negative at all four
corners contains no admissible point); c = 14.96 over [0, 1] × [0, 2] needs 414.
-/

namespace Work.Data.Moresco16Lower
open Work.Data.Moresco16

/-- Square root below its tangent: √y ≤ (y + s²)/(2s) for y ≥ 0 and s > 0. -/
theorem sqrt_le_tangent {y s : ℝ} (hy : 0 ≤ y) (hs : 0 < s) :
    Real.sqrt y ≤ (y + s ^ 2) / (2 * s) := by
  rw [le_div_iff₀ (by positivity)]
  have h := Real.sq_sqrt hy
  nlinarith [sq_nonneg (Real.sqrt y - s)]

/-- A quadratic with nonpositive discriminant relative to c: if α > 0 and β² ≤ α (γ − c), then
c ≤ α H₀² − 2 β H₀ + γ for every H₀. -/
theorem ge_of_disc {α β γ c H0 : ℝ} (hα : 0 < α) (hd : β ^ 2 ≤ α * (γ - c)) :
    c ≤ α * H0 ^ 2 - 2 * β * H0 + γ := by
  have h : 0 ≤ α * (α * H0 ^ 2 - 2 * β * H0 + γ - c) := by
    nlinarith [sq_nonneg (α * H0 - β)]
  have h2 := (mul_nonneg_iff_of_pos_left hα).1 h
  linarith

/-- One-dimensional step of `box_convex`: (u + v t)² − (w + x t) is convex in t, so if it is
≤ 0 at both ends of [t₀, t₁] it is ≤ 0 on the interval. -/
theorem seg_convex {u v w x t0 t1 t : ℝ} (h0 : t0 ≤ t) (h1 : t ≤ t1)
    (e0 : (u + v * t0) ^ 2 ≤ w + x * t0) (e1 : (u + v * t1) ^ 2 ≤ w + x * t1) :
    (u + v * t) ^ 2 ≤ w + x * t := by
  rcases eq_or_lt_of_le (le_trans h0 h1) with h | h
  · have : t = t0 := by linarith
    subst this; exact e0
  have key : (t1 - t0) * ((u + v * t) ^ 2 - (w + x * t)) =
      (t1 - t) * ((u + v * t0) ^ 2 - (w + x * t0)) + (t - t0) * ((u + v * t1) ^ 2 - (w + x * t1))
        - v ^ 2 * (t - t0) * (t1 - t) * (t1 - t0) := by ring
  have hA : (t1 - t) * ((u + v * t0) ^ 2 - (w + x * t0)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have hB : (t - t0) * ((u + v * t1) ^ 2 - (w + x * t1)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have hC : 0 ≤ v ^ 2 * (t - t0) * (t1 - t) * (t1 - t0) := by
    have := sq_nonneg v
    have h2 : 0 ≤ t - t0 := by linarith
    have h3 : 0 ≤ t1 - t := by linarith
    have h4 : 0 ≤ t1 - t0 := by linarith
    positivity
  have hle : (t1 - t0) * ((u + v * t) ^ 2 - (w + x * t)) ≤ 0 := by linarith
  by_contra hX
  have := mul_pos (sub_pos.2 h) (sub_pos.2 (not_le.1 hX))
  linarith

/-- Convexity on a box: (p + q m + r l)² ≤ a + b m + d l at the four corners of
[m₀, m₁] × [l₀, l₁] implies it at every point of the box. -/
theorem box_convex {p q r a b d m0 m1 l0 l1 m l : ℝ} (hm0 : m0 ≤ m) (hm1 : m ≤ m1)
    (hl0 : l0 ≤ l) (hl1 : l ≤ l1)
    (c00 : (p + q * m0 + r * l0) ^ 2 ≤ a + b * m0 + d * l0)
    (c01 : (p + q * m0 + r * l1) ^ 2 ≤ a + b * m0 + d * l1)
    (c10 : (p + q * m1 + r * l0) ^ 2 ≤ a + b * m1 + d * l0)
    (c11 : (p + q * m1 + r * l1) ^ 2 ≤ a + b * m1 + d * l1) :
    (p + q * m + r * l) ^ 2 ≤ a + b * m + d * l := by
  have e0 : (p + r * l0 + q * m) ^ 2 ≤ a + d * l0 + b * m :=
    seg_convex (u := p + r * l0) (w := a + d * l0) hm0 hm1
      (by linarith [c00, show (p + r * l0 + q * m0) = p + q * m0 + r * l0 by ring])
      (by nlinarith [c10])
  have e1 : (p + r * l1 + q * m) ^ 2 ≤ a + d * l1 + b * m :=
    seg_convex (u := p + r * l1) (w := a + d * l1) hm0 hm1 (by nlinarith [c01]) (by nlinarith [c11])
  have := seg_convex (u := p + q * m) (v := r) (w := a + b * m) (x := d) hl0 hl1
    (by nlinarith [e0]) (by nlinarith [e1])
  nlinarith [this]

/-- The χ² as a quadratic in H₀ when every E² is nonnegative. -/
theorem chiSqOL_eq (H0 Ωm ΩΛ : ℝ) (hy : ∀ i, 0 ≤ e2OL Ωm ΩΛ (m16Table i).1) :
    chiSqOL H0 Ωm ΩΛ =
      ((∑ i, e2OL Ωm ΩΛ (m16Table i).1 / (m16Table i).2.2 ^ 2) + 1 / 2.4 ^ 2) * H0 ^ 2
      - 2 * ((∑ i, (m16Table i).2.1 * Real.sqrt (e2OL Ωm ΩΛ (m16Table i).1) /
          (m16Table i).2.2 ^ 2) + 73 / 2.4 ^ 2) * H0
      + ((∑ i, (m16Table i).2.1 ^ 2 / (m16Table i).2.2 ^ 2) + 73 ^ 2 / 2.4 ^ 2) := by
  unfold chiSqOL
  have hterm : ∀ i, (H0 * Real.sqrt (e2OL Ωm ΩΛ (m16Table i).1) - (m16Table i).2.1) ^ 2 /
      (m16Table i).2.2 ^ 2 =
      e2OL Ωm ΩΛ (m16Table i).1 / (m16Table i).2.2 ^ 2 * H0 ^ 2
      - 2 * ((m16Table i).2.1 * Real.sqrt (e2OL Ωm ΩΛ (m16Table i).1) /
          (m16Table i).2.2 ^ 2) * H0
      + (m16Table i).2.1 ^ 2 / (m16Table i).2.2 ^ 2 := by
    intro i
    have hs := Real.sq_sqrt (hy i)
    set y := e2OL Ωm ΩΛ (m16Table i).1
    set e := Real.sqrt y
    rw [← hs]
    ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

end Work.Data.Moresco16Lower
