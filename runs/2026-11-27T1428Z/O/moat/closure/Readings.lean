import Mathlib

/-! # Target O, family moat: the three blind readings of run 2026-11-27T1428Z (brief 0ed6b5c), concatenated unchanged
apart from the repeated `import Mathlib` lines, so a closure can import them as one module. -/


namespace ReaderA

/-- A Gaussian prime: an irreducible element of `ℤ[i]` (Mathlib's `GaussianInt`). -/
def IsGaussianPrime (z : GaussianInt) : Prop := Irreducible z

/-- The vertex type of `G_D`: all Gaussian primes. -/
abbrev GaussianPrime : Type := {z : GaussianInt // IsGaussianPrime z}

/-- Euclidean distance `|z - w| = √N(z - w)`, with `N(a+bi) = a² + b²` (Mathlib's
`Zsqrtd.norm` for `d = -1`). -/
noncomputable def gdist (z w : GaussianInt) : ℝ :=
  Real.sqrt (((z - w).norm : ℤ) : ℝ)

lemma gdist_comm (z w : GaussianInt) : gdist z w = gdist w z := by
  unfold gdist
  rw [← neg_sub, Zsqrtd.norm_neg]

/-- `G_D`: vertices all Gaussian primes, an edge between distinct `z, w` iff `|z - w| ≤ D`. -/
def GD (D : ℝ) : SimpleGraph GaussianPrime where
  Adj z w := z ≠ w ∧ gdist z.1 w.1 ≤ D
  symm := ⟨fun _ _ h => ⟨h.1.symm, by rw [gdist_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Theorem 1.1: for every finite real `D` there is a finite `B_D` such that every connected
component of `G_D` has at most `B_D` vertices (in particular is finite). -/
theorem reading_thm_1_1 :
    ∀ D : ℝ, ∃ B : ℕ, ∀ c : (GD D).ConnectedComponent,
      c.supp.Finite ∧ c.supp.ncard ≤ B := sorry

/-- "Consequently": every sequence of distinct Gaussian primes whose successive distances are at
most `D` has at most `B_D` terms (finite sequences `p₀, …, p_{n-1}`, see comment block). -/
theorem reading_thm_1_1_consequently :
    ∀ D : ℝ, ∃ B : ℕ, ∀ (n : ℕ) (p : Fin n → GaussianInt),
      (∀ i, IsGaussianPrime (p i)) → Function.Injective p →
      (∀ (i : ℕ) (h : i + 1 < n), gdist (p ⟨i, by omega⟩) (p ⟨i + 1, h⟩) ≤ D) →
      n ≤ B := sorry

/-- Answer to the Gaussian moat (infinite-walk) question: no `G_D` contains an infinite path with
no repeated vertex. -/
theorem reading_no_infinite_path :
    ∀ D : ℝ, ¬ ∃ f : ℕ → GaussianPrime,
      Function.Injective f ∧ ∀ n, (GD D).Adj (f n) (f (n + 1)) := sorry

end ReaderA

/-
Reader A -- ambiguities and choices

1. "Gaussian prime = irreducible element of ℤ[i]": `Irreducible` in Mathlib's `GaussianInt`
   (excludes 0 and units; includes all associates, so primes on the coordinate axes such as
   `3`, `3i` and `1+i` are vertices, as the theorem insists).

2. Distance: literally `|z| = √N(z)`, so `|z - w| = √N(z - w)` via `Real.sqrt` of the integer
   norm cast to ℝ.  `Real.sqrt` is never applied to a negative number here (`N ≥ 0`), so its
   junk value at negatives does not matter.

3. "finite real D": `D : ℝ`, all reals including `D ≤ 0` and `D < 1` (then `G_D` has no edges
   and the claim is trivial with `B = 1`, as the text remarks).  "finite B_D": `B : ℕ` (a real
   bound is equivalent to its floor); `B` may depend on `D` only -- it is chosen before the
   component, matching "independent of the starting prime".

4. "every connected component of G_D has at most B_D vertices": Mathlib's
   `SimpleGraph.ConnectedComponent` and its vertex set `supp`.  To avoid the junk value
   `Set.ncard (infinite set) = 0`, finiteness of `supp` is asserted explicitly together with
   `ncard ≤ B`.

5. "Consequently ... sequence of distinct Gaussian primes whose successive distances are at most
   D has at most B_D terms":  read with finite sequences `Fin n → GaussianInt` (an infinite
   sequence is excluded as a consequence, since its first `B+1` terms would be a violating
   finite one; this is also covered by the third theorem).  "distinct" = injective;
   "successive distances" = `|p_i - p_{i+1}| ≤ D` for `i + 1 < n` (no ℕ subtraction: the
   index condition is `i + 1 < n`).  I stated it with its own `∃ B` rather than the same
   `B_D` as Theorem 1.1; since any bound for component sizes bounds such sequences (the terms
   of such a sequence lie in one component of `G_D`), the two are equivalent in content.
   For `n = 0, 1` there are no successive pairs; these are trivially bounded.

6. "infinite path with no repeated vertex in G_D": a one-sided sequence `f : ℕ → vertices`,
   injective, with consecutive terms adjacent in `G_D`.  (A two-sided infinite path contains
   a one-sided one, so this is the weakest form to negate.)  "answers negatively" is read as
   `∀ D, ¬ ∃ ...` ("some G_D contains" negated).  Adjacency in `G_D` already includes
   distinctness of consecutive terms, implied by injectivity anyway.

7. No junk values: no ℕ subtraction, no division, `ncard` guarded by `Finite`, no sSup/sInf,
   no ℕ∞.
-/


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


namespace ReaderC

/-- A Gaussian prime: an irreducible element of `ℤ[i] = GaussianInt`. -/
def IsGaussianPrime (z : GaussianInt) : Prop := Irreducible z

/-- Euclidean distance `|z - w| = √(N(z - w))` on `ℤ[i] ≅ ℤ²`, with `a + bi ↦ (a, b)`. -/
noncomputable def gdist (z w : GaussianInt) : ℝ :=
  Real.sqrt ((((z.re - w.re : ℤ) : ℝ)) ^ 2 + (((z.im - w.im : ℤ) : ℝ)) ^ 2)

/-- Edge of `G_D` between distinct `z, w` with `|z - w| ≤ D`. -/
def adjD (D : ℝ) (z w : GaussianInt) : Prop := z ≠ w ∧ gdist z w ≤ D

/-- `G_D`: vertices are the Gaussian primes, edges as in `adjD` between Gaussian primes. -/
def GD (D : ℝ) (z w : GaussianInt) : Prop :=
  IsGaussianPrime z ∧ IsGaussianPrime w ∧ adjD D z w

/-- The connected component of `z` in `G_D`, as a set of vertices. -/
def componentOf (D : ℝ) (z : GaussianInt) : Set GaussianInt :=
  {w | IsGaussianPrime w ∧ Relation.ReflTransGen (GD D) z w}

/-- Theorem 1.1: for every real `D` there is a natural `B` bounding the number of vertices of
every connected component of `G_D`. `encard` is used, so an infinite component would
give `⊤` and not a fake small number. -/
theorem reading_moat_thm1_1 :
    ∀ D : ℝ, ∃ B : ℕ, ∀ z : GaussianInt, IsGaussianPrime z →
      (componentOf D z).encard ≤ (B : ℕ∞) := by
  sorry

/-- "Consequently": every sequence of distinct Gaussian primes with successive distances at
most `D` has at most `B` terms (the same `B` as the theorem, depending on `D`). -/
theorem reading_moat_consequently :
    ∀ D : ℝ, ∃ B : ℕ, ∀ (n : ℕ) (p : Fin n → GaussianInt),
      Function.Injective p → (∀ i, IsGaussianPrime (p i)) →
      (∀ i j : Fin n, j.val = i.val + 1 → gdist (p i) (p j) ≤ D) →
      n ≤ B := by
  sorry

/-- Answer to the infinite-walk question: for no real `D` does `G_D` contain an infinite path
with no repeated vertex (an injective sequence of Gaussian primes with consecutive vertices
adjacent in `G_D`). -/
theorem reading_moat_no_infinite_path :
    ∀ D : ℝ, ¬ ∃ p : ℕ → GaussianInt, Function.Injective p ∧
      (∀ n, IsGaussianPrime (p n)) ∧ ∀ n, GD D (p n) (p (n + 1)) := by
  sorry

/-!
## Ambiguities and choices (reader C, O46)

1. Gaussian primes: "irreducible element of `ℤ[i]`", read literally as `Irreducible z` in
   Mathlib's `GaussianInt` (`Zsqrtd (-1)`). In a UFD this is the same as prime, but I kept the
   source's word.

2. Coordinates: `a + bi ↦ (a, b)` via `z.re`, `z.im`. The distance is the Euclidean one,
   `gdist z w = √((Δa)² + (Δb)²)`, computed in `ℝ` (the integer differences are cast to
   `ℝ` before squaring, so no `ℤ`-subtraction junk). `gdist` is `Real.sqrt`, so a negative
   `D` gives no edges; this matches "`|z - w| ≤ D`" for every real `D`.

3. "Finite real D": I quantified over all reals `D` (every real is finite in this sense).
   For `D < 0`, the edge relation is empty and the statements remain true.

4. Edges: `G_D` has the Gaussian primes as vertices, and an edge between DISTINCT `z, w` with
   `|z - w| ≤ D`. `adjD` requires `z ≠ w`. The graph `G_D` is `GD`, which also requires both
   endpoints to be Gaussian primes. "Connected component" is the set of primes reachable
   from `z` by `Relation.ReflTransGen (GD D)`; this is the usual connected component for
   the graph on the vertex set of primes.

5. Theorem 1.1 uses `Set.encard` (in `ℕ∞`), with `B : ℕ` cast into `ℕ∞`. An infinite
   component would have `encard = ⊤`, so the bound really says the component is finite
   with at most `B` vertices. This avoids the `Set.ncard` junk value (`ncard` of an
   infinite set is `0`).

6. "Consequently": I read "every sequence of distinct Gaussian primes whose successive
   distances are at most D has at most B_D terms" with finite sequences `Fin n → ℤ[i]`.
   Infinite sequences are not counted: an infinite such sequence is an infinite path, which
   is excluded by the same statement, so the finite version is what is claimed. "Distinct"
   is `Function.Injective`. "Successive distances at most D" is read as
   `gdist (p i) (p (i+1)) ≤ D` for consecutive indices. The bound is the same `B` as in the
   theorem, which depends only on `D`. `B` is chosen before the sequence.

7. Infinite-walk question: an infinite path with no repeated vertex in some `G_D` is an
   injective `ℕ → ℤ[i]` of Gaussian primes with each consecutive pair an edge of `G_D`. The
   answer stated is the negation (no `D`), as the abstract and text say.

8. Not written: the "nonexplicit" and "finite periodic sieve" remarks, and the `D < 1`
   remark (`B_D = 1`), which are not among the three claims the brief lists.
-/

end ReaderC
