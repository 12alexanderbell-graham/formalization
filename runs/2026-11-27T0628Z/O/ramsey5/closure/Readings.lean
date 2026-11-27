import Mathlib

/-! Blind readings A, B, C (code unchanged; only `import Mathlib` hoisted). -/

-- ===== reader A =====

/-!
# Blind reading A of O29: "The sharp logarithmic exponent of r(5,t)", Theorem 1.1

Source: `ramsey5/sources/introduction_lines1-29.tex`.
-/

namespace ReaderA

open Real Filter Topology

/-- "a simple graph on `n` vertices contains a complete graph `K_s`": some `s`-element vertex
set is pairwise adjacent. -/
def ContainsComplete {V : Type*} (G : SimpleGraph V) (s : ℕ) : Prop :=
  ∃ S : Finset V, S.card = s ∧ G.IsClique (S : Set V)

/-- "`G` contains an independent set of size `t`": some `t`-element vertex set is pairwise
non-adjacent. -/
def ContainsIndependent {V : Type*} (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∃ S : Finset V, S.card = t ∧ G.IsIndepSet (S : Set V)

/-- The Ramsey property for `n`: every simple graph on `n` vertices (vertex type `Fin n`)
contains either a `K_s` or an independent set of size `t`. -/
def RamseyProperty (s t n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), ContainsComplete G s ∨ ContainsIndependent G t

/-- The Ramsey number `r(s,t)`: the least integer `n` with `RamseyProperty s t n`.
(The source defines it for `s, t ≥ 2`; it is only used here with `s = 5` and `t` large.
The set is nonempty by Ramsey's theorem, so `sInf` returns the genuine least element.) -/
noncomputable def r (s t : ℕ) : ℕ :=
  sInf {n : ℕ | RamseyProperty s t n}

/-- Theorem 1.1, two-sided bound: there is an absolute constant `C > 0` such that for every
`ε > 0`, all sufficiently large integers `t` satisfy
`t^4 / (log t)^(3+ε) ≤ r(5,t) ≤ C t^4 / (log t)^3`. -/
theorem reading_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℕ in atTop,
      (t : ℝ) ^ 4 / (Real.log t) ^ ((3 : ℝ) + ε) ≤ (r 5 t : ℝ) ∧
      (r 5 t : ℝ) ≤ C * (t : ℝ) ^ 4 / (Real.log t) ^ 3 := sorry

/-- Theorem 1.1, consequence: `lim_{t→∞} (4 log t - log r(5,t)) / log log t = 3`. -/
theorem reading_limit :
    Tendsto (fun t : ℕ => (4 * Real.log t - Real.log (r 5 t)) / Real.log (Real.log t))
      atTop (𝓝 3) := sorry

end ReaderA

/-!
## Ambiguities and choices

1. *Definition of `r(s,t)`.* "Least integer `n` such that every simple graph on `n` vertices
   contains `K_s` or an independent set of size `t`". Graphs on `n` vertices are modelled as
   `SimpleGraph (Fin n)` (any `n`-vertex graph is isomorphic to one of these, and the property is
   isomorphism-invariant). "Contains `K_s`" = there is an `s`-element clique (a subgraph
   isomorphic to `K_s`); "independent set of size `t`" = a `t`-element pairwise non-adjacent
   set. I wrote these myself rather than using `CliqueFree`, to stay close to the wording.
2. *Junk value of `sInf`.* `sInf ∅ = 0` in `ℕ`. The set `{n | RamseyProperty s t n}` is nonempty
   for all `s, t` by Ramsey's theorem (e.g. `n = C(s+t-2, s-1)` works), so `r` is never the junk
   value. Moreover a junk `0` would make the lower bound in `reading_bounds` false, not vacuously
   true, so the statement cannot be trivialised by the junk value. The restriction `s,t ≥ 2` of
   the source is harmless: we only use `s = 5` and eventually-large `t`.
3. *"Absolute constant `C > 0` ... for every `ε > 0`, all sufficiently large `t`"*: quantifier
   order `∃ C > 0, ∀ ε > 0, ∀ᶠ t in atTop`. The threshold depends on `ε` (as the source says),
   while `C` does not depend on `ε`. Both inequalities are under the same threshold.
4. *Logarithms/powers.* Natural log `Real.log`. `(log t)^(3+ε)` is a real power (`rpow`) since `ε`
   is real; its base `log t` is positive once `t ≥ 2`, which holds eventually, so no `rpow` of
   a nonpositive base matters. `t^4` and `(log t)^3` are natural-number powers. Divisions by
   `(log t)^…` are by positive numbers eventually (so no `x/0 = 0` junk eventually).
5. *The limit.* `lim_{t→∞}` is over integers `t → ∞` (`atTop` on `ℕ`). For small `t`,
   `log (log t)` and `log r(5,t)` may take junk values (`log 0 = 0`, `log` of numbers ≤ 1, and
   division by `0`), but a limit only depends on large `t`, where `log log t > 0` and
   `r(5,t) ≥ 1`, so these are irrelevant.
6. The theorem is stated as two separate theorems as the brief requires; "Consequently" is not
   formalised as an implication — the limit is stated on its own.
-/

-- ===== reader B =====

open Filter Topology

namespace ReaderB

/-- `r s t`: least `n` such that every simple graph on `n` vertices contains `K_s`
or an independent set of size `t`. -/
noncomputable def r (s t : ℕ) : ℕ :=
  sInf {n : ℕ | ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree s ∨ ¬ Gᶜ.CliqueFree t}

/-- Theorem 1.1, two-sided bound. -/
theorem reading_ramsey5_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℕ in atTop,
        (t : ℝ) ^ 4 / Real.log t ^ ((3 : ℝ) + ε) ≤ (r 5 t : ℝ) ∧
        (r 5 t : ℝ) ≤ C * ((t : ℝ) ^ 4 / Real.log t ^ (3 : ℕ)) := sorry

/-- Theorem 1.1, the limit. -/
theorem reading_ramsey5_limit :
    Tendsto (fun t : ℕ => (4 * Real.log t - Real.log (r 5 t)) / Real.log (Real.log t))
      atTop (𝓝 3) := sorry

/-
Ambiguities / choices.
* r(s,t) is `sInf` of a set of naturals; for s,t ≥ 2 the set is nonempty (Ramsey's theorem), so no
  junk value arises for the s=5, t≥2 cases used. Independent set of size t is encoded as a t-clique
  in the complement `Gᶜ` (`¬ Gᶜ.CliqueFree t`). Graphs on `Fin n`; the property is monotone in n so
  "least n" is the same as the source's. The source's hypothesis s,t ≥ 2 is not enforced in the def.
* "all sufficiently large integers t": `∀ᶠ t : ℕ in atTop`, with the threshold depending on ε
  (the quantifier order ∃ C, ∀ ε is as in the source: C is independent of ε).
* Logs: `Real.log`, natural. For large t, log t > 1 so the rpow base is positive and
  log log t > 0; the junk values of log/rpow for small arguments only matter for small t, which
  `∀ᶠ` / `Tendsto` ignore. Exponent 3+ε is a real power (`rpow`); (log t)^3 is a natural power.
  Positivity of r 5 t (so log (r 5 t) is not junk) holds for t ≥ 2 and is part of what is claimed.
* The limit is stated as an independent theorem (not as a consequence), as in the brief.
-/

end ReaderB

-- ===== reader C =====

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
