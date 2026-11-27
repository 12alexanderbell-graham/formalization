import Mathlib

namespace ReaderB

/-- Euclidean distance between Gaussian integers identified with points of `ℤ²`. -/
noncomputable def gdist (z w : GaussianInt) : ℝ :=
  Real.sqrt (((z.re - w.re : ℤ) : ℝ) ^ 2 + ((z.im - w.im : ℤ) : ℝ) ^ 2)

/-- Gaussian primes: irreducible elements of `ℤ[i]`. -/
abbrev GPrime := {z : GaussianInt // Irreducible z}

/-- `G_D`: vertices all Gaussian primes, edge between distinct `z, w` if `|z - w| ≤ D`. -/
noncomputable def GD (D : ℝ) : SimpleGraph GPrime where
  Adj z w := z ≠ w ∧ gdist z.1 w.1 ≤ D
  symm := ⟨fun z w ⟨h1, h2⟩ => ⟨h1.symm, by
    unfold gdist at *
    convert h2 using 2 <;> push_cast <;> ring⟩⟩
  loopless := ⟨fun z h => h.1 rfl⟩

/-- Theorem 1.1: uniform component bound.  Every component has at most `B` vertices
(`encard` in `ℕ∞`, so infinite components exceed every `B`). -/
theorem reading_moat_uniform_bound (D : ℝ) :
    ∃ B : ℕ, ∀ v : GPrime, {w : GPrime | (GD D).Reachable v w}.encard ≤ B := sorry

/-- "Consequently": sequences of distinct Gaussian primes with successive distances ≤ D have at most
`B_D` terms (where `B_D` is the bound above; stated as existence of a bound for each `D`). -/
theorem reading_moat_sequences (D : ℝ) :
    ∃ B : ℕ, ∀ (n : ℕ) (f : Fin n → GaussianInt), (∀ i, Irreducible (f i)) → Function.Injective f →
      (∀ (i : Fin n) (h : i.val + 1 < n), gdist (f i) (f ⟨i.val + 1, h⟩) ≤ D) → n ≤ B := sorry

/-- The infinite-walk question, answered negatively: no `G_D` has an infinite path (an injective
`ℕ`-indexed sequence of Gaussian primes with consecutive distances ≤ D). -/
theorem reading_moat_no_infinite_walk :
    ¬ ∃ (D : ℝ) (f : ℕ → GaussianInt), (∀ n, Irreducible (f n)) ∧ Function.Injective f ∧
      ∀ n, gdist (f n) (f (n + 1)) ≤ D := sorry

end ReaderB

/-
Ambiguities and choices.
* Gaussian integers: Mathlib's `GaussianInt = ℤ√-1` with `re`, `im`; `a+bi ↔ (a,b)`.  Gaussian prime =
  `Irreducible` (as the text defines it).  Distance = `√((Δre)² + (Δim)²)` computed in ℝ (casts from ℤ).
* `G_D` as `SimpleGraph` on the subtype of Gaussian primes; adjacency requires `z ≠ w` and distance ≤ D.
  `D : ℝ` arbitrary ("finite real"; negative or tiny D give no edges, harmless).
* Component size: "at most B_D vertices" stated as `Set.encard` of the set of vertices reachable from v
  (the component) `≤ (B : ℕ∞)`.  `encard` of an infinite set is ⊤ which exceeds every natural number,
  so an infinite component cannot satisfy it; no `ncard`/`sSup` junk.  B is a natural number (finite).
  "Every connected component" is quantified as "every v's component", equivalent.
* Sequence theorem: sequences are `Fin n → GaussianInt` (n arbitrary, including 0), all irreducible,
  injective (distinct), consecutive distances ≤ D (direct distance, not Adj, same thing given distinctness).
  The bound B is existentially quantified after D (the same `B_D` as in the first theorem is not
  literally tied; it is only claimed per-D).
* Infinite walk: a one-way infinite injective sequence `ℕ → GaussianInt` of primes with steps ≤ D; the text's
  "infinite path with no repeated vertex" read as a ray (two-way infinite paths contain rays, so the
  negation is equivalent).  The answer is the negation over all D.
* No subtraction in ℕ (the only subtraction is ℤ-valued, before cast), no division.
-/
