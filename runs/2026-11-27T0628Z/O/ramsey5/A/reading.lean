import Mathlib

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
