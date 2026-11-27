import Mathlib

namespace ReaderA

/-!
# Blind reading A, family O2: "Catalan's constant is irrational"

Source (introduction.tex, lines 3--8, 16--18):
  G = β(2) = ∑_{j=0}^∞ (-1)^j / (2j+1)^2,   β(s) = ∑_{j=0}^∞ (-1)^j / (2j+1)^s  (s > 0),
  equivalently L(2, χ_{-4}) for the odd quadratic character of conductor 4.
  Theorem: Catalan's constant is irrational.
-/

namespace BlindReadingA.Catalan

/-- The `j`-th term `(-1)^j / (2j+1)^2` of the source's series for `G`. -/
noncomputable def catalanTerm (j : ℕ) : ℝ := (-1 : ℝ) ^ j / ((2 * j + 1 : ℝ) ^ 2)

/-- The series is absolutely convergent: `|(-1)^j/(2j+1)^2| ≤ 1/(j+1)^2`, and `∑ 1/(n+1)^2`
converges (p-series, p = 2). Hence it is `Summable` in Lean's (unconditional) sense, so the
`tsum` below is the genuine sum, not the junk value `0`. -/
theorem summable_catalanTerm : Summable catalanTerm := by
  have hg : Summable (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    simpa [Nat.cast_add, Nat.cast_one] using this
  refine Summable.of_norm_bounded hg (fun j => ?_)
  have h1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have h2 : ((j : ℝ) + 1) ^ 2 ≤ (2 * (j : ℝ) + 1) ^ 2 := by
    have : (j : ℝ) + 1 ≤ 2 * j + 1 := by have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith
    exact pow_le_pow_left₀ h1.le this 2
  rw [catalanTerm, Real.norm_eq_abs, abs_div, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_pos (by positivity)]
  exact one_div_le_one_div_of_le (by positivity) h2

/-- Catalan's constant `G = ∑_{j=0}^∞ (-1)^j / (2j+1)^2` (source, line 5). -/
noncomputable def CatalanConstant : ℝ := ∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℝ) ^ 2)

/-- Non-junk check: `CatalanConstant` really is the sum of the series. -/
theorem hasSum_CatalanConstant :
    HasSum (fun j : ℕ => (-1 : ℝ) ^ j / ((2 * j + 1 : ℝ) ^ 2)) CatalanConstant :=
  summable_catalanTerm.hasSum

/-- Dirichlet beta, `β(s) = ∑_{j≥0} (-1)^j/(2j+1)^s` for real `s`. The source allows `s > 0`,
but for `0 < s ≤ 1` the series converges only conditionally, so Lean's `tsum` would return the
junk value `0` there. We only use `β(2)`, where the series converges absolutely. -/
noncomputable def dirichletBeta (s : ℝ) : ℝ := ∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℝ) ^ s)

/-- `G = β(2)` (source, line 5). Proved by `simp` (`rpow` with exponent `2` is `^ 2`). -/
theorem CatalanConstant_eq_dirichletBeta_two : CatalanConstant = dirichletBeta 2 := by
  simp [CatalanConstant, dirichletBeta]

/-- The odd quadratic character of conductor 4, `χ_{-4}`, valued in `ℂ`
(Mathlib's `ZMod.χ₄ : MulChar (ZMod 4) ℤ`, composed with `ℤ → ℂ`). -/
noncomputable def chiMinus4 : ZMod 4 → ℂ := fun x => (ZMod.χ₄ x : ℂ)

/-- Non-junk check: the L-series of `χ_{-4}` converges absolutely at `s = 2`. -/
theorem LSeriesSummable_chiMinus4_two : LSeriesSummable (fun n : ℕ => chiMinus4 n) 2 :=
  ZMod.LSeriesSummable_of_one_lt_re chiMinus4 (by norm_num)

/-- Main theorem (source, Theorem 1.1 / thm:main): Catalan's constant is irrational. -/
theorem reading : Irrational CatalanConstant := sorry

/-- Second equivalent definition from the source (line 9--10): `G = L(2, χ_{-4})`, with
`L(s, χ) = ∑_{n≥1} χ(n) n^{-s}` (Mathlib's `LSeries`). Stated as the source asserts it
("equivalently"); not proved here. -/
theorem reading_alt : (CatalanConstant : ℂ) = LSeries (fun n : ℕ => chiMinus4 n) 2 := sorry

end BlindReadingA.Catalan

/-!
## Ambiguities and choices (reader A)

1. Symbol clash: the source calls Catalan's constant `G`; we name it `CatalanConstant`.
2. Definition used: the explicit series `∑_{j≥0} (-1)^j/(2j+1)^2` over `j : ℕ`, in `ℝ`, written
   as a `tsum`. Junk-value check: Lean's `tsum` is `0` unless the family is (unconditionally)
   summable. Here it is absolutely summable (bound `1/(j+1)^2`, p-series with p = 2), proved in
   `summable_catalanTerm`, so `hasSum_CatalanConstant` holds and the value is the true sum
   (≈ 0.9159655...). No `sorry` is used in these facts.
3. `β(s)` for `s > 0`: for `0 < s ≤ 1` the alternating series is only conditionally convergent,
   and Lean's `tsum` would give `0` (junk). We define `dirichletBeta` for all real `s` but only
   ever evaluate it at `s = 2`, where it agrees with the definition (proved, no `sorry`). A faithful
   `β` for `0 < s ≤ 1` would need a limit of partial sums (or analytic continuation); not needed.
4. `L(2, χ_{-4})`: "the odd quadratic character of conductor 4" is the unique nontrivial character
   mod 4, `χ(n) = 0` for even `n`, `1` for `n ≡ 1 (4)`, `-1` for `n ≡ 3 (4)`; this is Mathlib's
   `ZMod.χ₄`. We use the plain `LSeries` (not `DirichletCharacter.LFunction`, the analytic
   continuation), which is legitimate because at `s = 2` the L-series converges absolutely
   (`LSeriesSummable_chiMinus4_two`, proved), so `LSeries` is not junk there. The equation
   `G = L(2, χ_{-4})` is stated (`reading_alt`) with `sorry`: the source states it as a known
   equivalence, not as something it proves. It is a reindexing `n = 2j+1`.
5. "Irrational" read as Mathlib's `Irrational x := x ∉ Set.range ((↑) : ℚ → ℝ)`.
6. Proved vs stated: the source proves only "Catalan's constant is irrational" (`reading`). The
   identities `G = β(2) = L(2, χ_{-4})` are definitions/recalled facts, not claims of the paper.
-/
end ReaderA

namespace ReaderB

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
end ReaderB

namespace ReaderC

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
end ReaderC
