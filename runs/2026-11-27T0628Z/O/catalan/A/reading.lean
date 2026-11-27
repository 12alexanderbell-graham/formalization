import Mathlib

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
