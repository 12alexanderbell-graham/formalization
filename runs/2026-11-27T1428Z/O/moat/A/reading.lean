import Mathlib

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
