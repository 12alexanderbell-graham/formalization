import Mathlib

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
