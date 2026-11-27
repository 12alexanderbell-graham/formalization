import Mathlib

/-!
Reading C of O29: "The sharp logarithmic exponent of r(5,t)" (only the excerpt
`ramsey5/sources/introduction_lines1-29.tex` was read).
-/

open Filter Topology

namespace ReaderC

/-- `IsRamseyGood s t n`: every simple graph on the vertex type `Fin n` contains a
clique of size `s` or an independent set of size `t`. -/
def IsRamseyGood (s t n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n),
    (∃ S : Finset (Fin n), S.card = s ∧ G.IsClique (S : Set (Fin n))) ∨
    (∃ S : Finset (Fin n), S.card = t ∧ G.IsIndepSet (S : Set (Fin n)))

/-- The Ramsey number `r(s,t)` as the least `n` with `IsRamseyGood s t n`. -/
noncomputable def ramsey (s t : ℕ) : ℕ :=
  sInf {n : ℕ | IsRamseyGood s t n}

/-- Theorem 1.1, two-sided bound. There is an absolute constant `C > 0` such that for every
`ε > 0`, all sufficiently large `t` satisfy
`t^4 / (log t)^(3+ε) ≤ r(5,t) ≤ C t^4 / (log t)^3`. -/
theorem reading_ramsey5_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℕ in atTop,
        (t : ℝ) ^ 4 / (Real.log t) ^ ((3 : ℝ) + ε) ≤ (ramsey 5 t : ℝ) ∧
        (ramsey 5 t : ℝ) ≤ C * (t : ℝ) ^ 4 / (Real.log t) ^ 3 := by
  sorry

/-- Theorem 1.1, limit statement:
`lim_{t→∞} (4 log t - log r(5,t)) / log log t = 3`. -/
theorem reading_ramsey5_limit :
    Tendsto (fun t : ℕ =>
      (4 * Real.log t - Real.log (ramsey 5 t : ℝ)) / Real.log (Real.log t))
      atTop (𝓝 3) := by
  sorry

end ReaderC

/-
Ambiguities and choices (Reader C, O29):

1. Graphs on n vertices: modelled as `SimpleGraph (Fin n)`, which is the standard
   reading of "every simple graph on n vertices" up to isomorphism.
2. `K_s` containment: "contains a complete graph K_s" is read as: there is a set of
   exactly `s` vertices that is a clique (`G.IsClique`). Independent sets of size `t` are
   read the same way with `G.IsIndepSet` and `S.card = t`.
3. `r(s,t)` is defined as `sInf` of the set of `n` with `IsRamseyGood s t n`. Junk-value
   check: this set is nonempty for `s,t ≥ 2` (Ramsey's theorem), so `sInf` is the
   genuine least element and not the junk value `0` of `sInf ∅`. The file does not prove
   this; it is only needed to make `ramsey` the intended number. Since the excerpt says
   s,t ≥ 2 but the theorem only concerns `s = 5`, no hypothesis on s,t is stated in the
   definition.
4. `t` ranges over `ℕ` (the excerpt says "integers t"; the bound is only asymptotic, so
   `t` is taken to tend to infinity in `ℕ`). `r(5,t)` is cast to `ℝ` in the inequalities
   and in the limit.
5. Natural logarithm: `Real.log` (the excerpt says "All logarithms are natural").
6. The two-sided bound. Order of quantifiers as in the excerpt: first `C` (absolute, so
   before `ε`), then for every `ε > 0` all sufficiently large `t` (so `∀ᶠ t` after `ε`).
   The exponent `3+ε` is a real exponent, hence `Real.rpow` (`^ ((3:ℝ)+ε)`). Junk values:
   `Real.log t` is nonpositive for `t = 0, 1`, where rpow/division junk appears, but the
   statement is only claimed eventually (`∀ᶠ`), so these values are irrelevant.
   `t^4` and `(log t)^3` are natural powers. The constant `C` is required to be positive.
7. The limit: `(4 log t - log r(5,t)) / log log t` tends to `3` along `t → ∞` in `ℕ`.
   Junk values: for small `t`, `log log t` may be `0` or negative (Lean's division by 0
   gives 0), but `Tendsto` ignores finitely many `t`, so this is harmless.
8. The excerpt's "Consequently," phrasing: the limit is recorded as a second theorem, as
   the brief requests, and is not derived from the bound inside Lean.
9. Not formalized: nothing else in the excerpt (the remark that the theorem "leaves open a
   constant-factor asymptotic") is a claim, so it is not included.
-/
