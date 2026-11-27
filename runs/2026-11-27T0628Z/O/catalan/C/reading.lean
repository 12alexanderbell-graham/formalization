import Mathlib

/-!
Blind reading of family O2 ("Catalan's constant is irrational"), reader C.
Source: `catalan/sources/introduction_lines1-18.tex`.
-/

/-- Catalan's constant `G = β(2) = ∑_{j≥0} (-1)^j / (2j+1)^2`, the source's first displayed
definition. The source writes `(2j+1)^2`, an integer power, so we use `^ 2` on `ℝ`. -/
noncomputable def CatalanConstant : ℝ :=
  ∑' j : ℕ, (-1 : ℝ) ^ j / (2 * (j : ℝ) + 1) ^ 2

/-- The series converges absolutely: `|(-1)^j/(2j+1)^2| = 1/(2j+1)^2 ≤ 1/(j+1)^2`, and
`∑ 1/(j+1)^2` converges (p-series with p = 2). Hence the series is `Summable`, so `tsum` returns
its genuine sum rather than the junk value `0` that `tsum` gives to non-summable families. -/
lemma catalan_summable :
    Summable (fun j : ℕ => (-1 : ℝ) ^ j / (2 * (j : ℝ) + 1) ^ 2) := by
  apply Summable.of_norm
  have h : Summable (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    simpa using this
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_) h
  rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, norm_pow,
    Real.norm_of_nonneg (by positivity)]
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith [sq_nonneg (j : ℝ), (Nat.cast_nonneg j : (0:ℝ) ≤ j)]

/-- The `tsum` defining `CatalanConstant` is the honest sum: `HasSum` holds for it. -/
lemma catalan_hasSum :
    HasSum (fun j : ℕ => (-1 : ℝ) ^ j / (2 * (j : ℝ) + 1) ^ 2) CatalanConstant :=
  catalan_summable.hasSum

/-- Main claim, as stated in the source (`thm:main`): Catalan's constant is irrational. -/
theorem reading : Irrational CatalanConstant := sorry

/-- Second definition in the source: `β(s) = ∑_{j≥0} (-1)^j/(2j+1)^s` for `s > 0`, with real
powers. At `s = 2` this is `CatalanConstant`; the source calls it the same number. -/
noncomputable def dirichletBeta (s : ℝ) : ℝ :=
  ∑' j : ℕ, (-1 : ℝ) ^ j / (2 * (j : ℝ) + 1) ^ s

/-- `β(2)` (real power `s = 2`) agrees with `CatalanConstant`. -/
lemma dirichletBeta_two : dirichletBeta 2 = CatalanConstant := by
  unfold dirichletBeta CatalanConstant
  simp

/-- Alternative definition `G = β(2)`: irrationality of the value of `β` at `s = 2`. -/
theorem reading_alt : Irrational (dirichletBeta 2) := by
  rw [dirichletBeta_two]
  exact reading

/-- Third description in the source: `G = L(2, χ₋₄)`, the L-series at `s = 2` of the odd
quadratic character of conductor 4. Mathlib's `ZMod.χ₄ : MulChar (ZMod 4) ℤ` is exactly that
character (`χ(1) = 1`, `χ(3) = -1`, `χ(0) = χ(2) = 0`), and we lift it to `ℕ → ℂ` through
the reduction `ℕ → ZMod 4`. Stated as: the value is some real number, and that number is
irrational. -/
theorem reading_alt_L :
    ∃ x : ℝ, LSeries (fun n : ℕ => (((ZMod.χ₄ (n : ZMod 4)) : ℤ) : ℂ)) 2 = (x : ℂ) ∧
      Irrational x := sorry

/-!
## Ambiguities and choices (reader C)

1. Definition: `CatalanConstant` uses `∑' j : ℕ` over `j ≥ 0` with `(2j+1)^2` as an integer
   power. The source's second form `β(s)` uses real powers `(2j+1)^s`; I kept that as
   `dirichletBeta` and proved (in the file, not sorry) that `dirichletBeta 2 = CatalanConstant`
   via `Real.rpow_two`.
2. Convergence: the series converges absolutely (`catalan_summable`, proved, no sorry).
   Lean's `tsum` is not a junk 0 here, because `catalan_hasSum` shows `HasSum` holds.
3. `Irrational` is Mathlib's: `x ∉ Set.range (Rat.cast)`, a real-number predicate.
4. `reading_alt_L`: the source does not fix a Lean-level encoding of `L(2, χ₋₄)`. I used
   Mathlib's `LSeries`, which is `∑' n, term f s n` and gives junk `0` for non-absolutely
   convergent series. For `s = 2` the series is absolutely convergent, so the junk value is
   not what gets stated here, but I did not prove that in this file. I used `ZMod.χ₄` (values in `ℤ`) cast to `ℂ`,
   and the existential `∃ x : ℝ` to express "this value is a real irrational number".
   The source's "equivalently" is the same number, so this is the same claim, not a new one.
5. `theorem reading` and `reading_alt_L` use `sorry`; only the statements are checked.
6. Source status: the source's Theorem `thm:main` is stated as a theorem (a proved claim).
   The excerpt does not show its proof, so my reading is "claimed proved in the source".
   The definitions are taken verbatim, nothing is a consequence.
-/
