import Mathlib

/-- Catalan's constant `G = β(2) = ∑_{j≥0} (-1)^j / (2j+1)^2`.
The series is absolutely convergent (terms bounded by `1/(2j+1)^2 ≤ 1/(j+1)^2`-ish, a
convergent p-series), so it is `Summable` and Lean's `tsum` is the true sum, not junk `0`.
(Value ≈ 0.9159..., nonzero.) -/
noncomputable def CatalanConstant : ℝ :=
  ∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℝ) ^ 2)

/-- Dirichlet beta function for real `s > 0` as in the source (only meaningful, as a convergent
series, for `s > 0`; for `s ≤ 1` convergence is conditional and `tsum` would be junk 0, so
we only use it at `s = 2`). -/
noncomputable def dirichletBeta (s : ℝ) : ℝ :=
  ∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℝ) ^ s)

theorem reading : Irrational CatalanConstant := sorry

/-- Second description: `G = β(2)`. -/
theorem reading_alt : Irrational (dirichletBeta 2) := sorry

/-- Third description: `G = L(2, χ₋₄)`, with `χ₋₄ = ZMod.χ₄` the odd quadratic character of
conductor 4 (as an ℤ-valued character cast to ℂ), `LSeries` the Dirichlet series
`∑ χ(n) n^{-s}`. Irrationality of the complex number: it is not the image of a rational. -/
theorem reading_L : ∀ q : ℚ,
    LSeries (fun n : ℕ => ((ZMod.χ₄ (n : ZMod 4) : ℤ) : ℂ)) 2 ≠ (q : ℂ) := sorry

/-
AMBIGUITIES / CHOICES
* Source gives G = β(2) = sum_{j>=0}(-1)^j/(2j+1)^2, and says it equals L(2, chi_{-4}); I define
  CatalanConstant by the first formula directly over ℝ.
* Convergence: absolutely, comparison with ∑ 1/n^2; hence Summable, tsum is the genuine sum.
* beta(s) stated for s>0; for 0<s≤1 it is only conditionally convergent so Lean tsum would give
  junk 0; I only instantiate at s=2 (rpow with real exponent 2 agrees with the nat power).
* "L(2, chi_{-4})": I used Mathlib's ZMod.χ₄ (values 0,1,-1 on ZMod 4; odd, conductor 4) and
  LSeries. Lean's LSeries is a tsum, junk-0 only if not summable; it is summable at s=2.
  Irrationality of a complex number has no Mathlib predicate, so stated as "≠ every rational".
  Note ZMod.χ₄ vs the source's chi_{-4}: same character (χ(1)=1, χ(3)=-1).
* 0^0 not an issue: (-1)^j with j : ℕ.
-/
