import Mathlib

/-! Target 0(b): the arithmetic of the one-loop entropy coefficient in Chandrasekaran,
arXiv 2611.34924, Section 4.7 (Eqs. bfent:schwarzschild-trace-one-loop:c, bfent:schwarzschild-clock-one-loop,
bfent:schwarzschild-fixed-mass-coefficient, footnote bfent:clock-logarithmic-coefficient and the bounds
bfent:canonical-clock-depth:b,c). Exact arithmetic only; the physics inputs (the 53/45 heat-kernel
coefficient, Gauss–Bonnet ∫R = 8π, the measure factor) are taken as printed. -/

namespace ExternalT0.Entropy
open Real

/-- (…c): `53/(45 (4π)²) · (8π · 8π) · log(s^{1/2}) = (106/45) log s`. -/
theorem one_loop_coeff (L : ℝ) :
    53 / (45 * (4 * π) ^ 2) * (8 * π * (8 * π)) * (L / 2) = 106 / 45 * L := by
  have : π ≠ 0 := Real.pi_ne_zero
  field_simp; ring

/-- The measure adds 1/2 to the power; with `s ∝ ℓ²`, `log Z = (q/(1-q)) log ℓ` gives
`q/(1-q) = 2 (106/45 + 1/2)`, hence `q = 257/302`. -/
theorem q_value (q : ℝ) (hq : q ≠ 1) :
    q / (1 - q) = 2 * (106 / 45 + 1 / 2) ↔ q = 257 / 302 := by
  have h1 : (1 - q) ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  rw [div_eq_iff h1]; constructor <;> intro h <;> linarith

/-- Fixed-mass coefficient: `q/(2(1-q)) − 1/2 = 106/45` at `q = 257/302`, i.e. `(212/45) ln a`
with `s ∝ a²`, which is Sen's `C_local = 424/90` for pure gravity (his mixed ensemble, J summed). -/
theorem fixed_mass : (257 / 302 : ℝ) / (2 * (1 - 257 / 302)) - 1 / 2 = 106 / 45 ∧
    (106 / 45 : ℝ) * 2 = 424 / 90 := by norm_num

/-- Footnote: `q = x²(2 − q)` forces `q = 2x²/(1+x²)` and `q/(2(1−q)) = x²/(1−x²)`. -/
theorem footnote_q (x q : ℝ) (hx : x ^ 2 < 1) (h : q = x ^ 2 * (2 - q)) :
    q = 2 * x ^ 2 / (1 + x ^ 2) ∧ q / (2 * (1 - q)) = x ^ 2 / (1 - x ^ 2) := by
  have h1 : 1 + x ^ 2 ≠ 0 := by positivity
  have hq : q = 2 * x ^ 2 / (1 + x ^ 2) := by field_simp; linarith
  refine ⟨hq, ?_⟩
  have h2 : 1 - x ^ 2 ≠ 0 := by linarith
  have h3 : 1 - 2 * x ^ 2 / (1 + x ^ 2) = (1 - x ^ 2) / (1 + x ^ 2) := by field_simp; ring
  rw [hq, h3]; field_simp

/-- The one-loop value and the footnote's `q(x)` together fix the ratio: `x² = 257/347`, i.e.
`ℓ(𝒟)/r_h = (1−ε)√(347/257)`. (A referee check, run 2026-11-26T1529Z, showed this is not a
contradiction: `r_h` is defined by `4π r_h² = ⟨Â⟩` in the clock-truncated state, so `x` is an output
of the state, not a free choice; the paper does not state the implied value.) -/
theorem footnote_vs_one_loop (x : ℝ) : 2 * x ^ 2 / (1 + x ^ 2) = 257 / 302 ↔ x ^ 2 = 257 / 347 := by
  have h1 : 1 + x ^ 2 ≠ 0 := by positivity
  rw [div_eq_iff h1]; constructor <;> intro h <;> linarith

/-- Consistency window: the paper's bounds `x² ≤ q ≤ x` (Eqs. canonical-clock-depth:b,c, with
`x = (1−ε) r_h/ℓ(𝒟)`) admit `q = 257/302` exactly for `257/302 ≤ x ≤ √(257/302)`; the implied
`x = √(257/347) ≈ 0.861` lies inside. -/
theorem bounds_window (x : ℝ) (hx : 0 ≤ x) :
    (x ^ 2 ≤ 257 / 302 ∧ (257 / 302 : ℝ) ≤ x) ↔ (257 / 302 ≤ x ∧ x ≤ Real.sqrt (257 / 302)) := by
  rw [Real.le_sqrt hx (by norm_num)]; tauto

/-- So a state with `x ≤ (1−ε)/2` (an average horizon radius at most half the maximum clock reading)
is incompatible with the one-loop value. -/
theorem example_excluded (ε : ℝ) (hε : 0 ≤ ε) :
    ¬ ((257 / 302 : ℝ) ≤ (1 - ε) * (1 / 2)) := by
  intro h; nlinarith

theorem implied_x_in_window : (257 / 302 : ℝ) ≤ Real.sqrt (257 / 347) ∧
    Real.sqrt (257 / 347) ≤ Real.sqrt (257 / 302) := by
  constructor
  · rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  · exact Real.sqrt_le_sqrt (by norm_num)

end ExternalT0.Entropy
#print axioms ExternalT0.Entropy.one_loop_coeff
#print axioms ExternalT0.Entropy.footnote_q
#print axioms ExternalT0.Entropy.bounds_window
