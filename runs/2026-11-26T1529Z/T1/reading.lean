import Mathlib

open scoped ContDiff
open Set MeasureTheory

namespace Reading

/-- Physical space ℝ³. -/
abbrev E := EuclideanSpace ℝ (Fin 3)

/-- The j-th unit vector e_j. -/
noncomputable def e (j : Fin 3) : E := EuclideanSpace.single j 1

/-- The closed half space-time ℝ³ × [0,∞), the domain "x ∈ ℝ^n, t ≥ 0". -/
def S : Set (E × ℝ) := univ ×ˢ Ici (0 : ℝ)

/-- Partial derivative ∂_j of a scalar function of x (derivative in direction e_j).
Only used on functions that are smooth on all of E, so `fderiv` is the genuine derivative. -/
noncomputable def pd (j : Fin 3) (g : E → ℝ) : E → ℝ := fun x => fderiv ℝ g x (e j)

/-- "(6) p, u ∈ C^∞(ℝ^n × [0,∞))" (also (11)): a function of (x,t) is C^∞ on the closed
half space-time, in the sense of `ContDiffOn` on `S` (whose derivatives within `S` are the
genuine one-sided-in-t derivatives, since `S` has unique differentials). -/
def SmoothOnS {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : E → ℝ → F) : Prop :=
  ContDiffOn ℝ ∞ (fun z : E × ℝ => g z.1 z.2) S

/-- "u° is a given C^∞ divergence-free vector field on ℝ^n":
smooth, and (2)-type condition Σ_i ∂_i u°_i = 0. -/
def SmoothDivFree (u0 : E → E) : Prop :=
  ContDiff ℝ ∞ u0 ∧ ∀ x, ∑ i, pd i (fun y => u0 y i) x = 0

/-- "(4) |∂_x^α u°(x)| ≤ C_{αK} (1+|x|)^{−K} on ℝ^n, for any α and K."
Encoded with the order-k Fréchet derivative norm (equivalent to all multi-indices of order k)
and the bound in the multiplied form (1+|x|)^K ‖D^k u°(x)‖ ≤ C. -/
def Decay4 (u0 : E → E) : Prop :=
  ∀ (k K : ℕ), ∃ C : ℝ, ∀ x : E, (1 + ‖x‖) ^ K * ‖iteratedFDeriv ℝ k u0 x‖ ≤ C

/-- "(5) |∂_x^α ∂_t^m f(x,t)| ≤ C_{αmK} (1+|x|+t)^{−K} on ℝ^n × [0,∞), for any α, m, K."
Encoded with the total derivative of order N in (x,t) within `S` (controls all mixed
∂_x^α ∂_t^m with |α|+m = N, and conversely). Requires `SmoothOnS f` to be meaningful. -/
def Decay5 (f : E → ℝ → E) : Prop :=
  ∀ (N K : ℕ), ∃ C : ℝ, ∀ (x : E) (t : ℝ), 0 ≤ t →
    (1 + ‖x‖ + t) ^ K * ‖iteratedFDerivWithin ℝ N (fun z : E × ℝ => f z.1 z.2) S (x, t)‖ ≤ C

/-- "(9) |∂_x^α ∂_t^m f(x,t)| ≤ C_{αmK} (1+|t|)^{−K} on ℝ³ × [0,∞), for any α, m, K."
Same encoding as `Decay5`, with weight (1+|t|)^K and uniform in x. -/
def Decay9 (f : E → ℝ → E) : Prop :=
  ∀ (N K : ℕ), ∃ C : ℝ, ∀ (x : E) (t : ℝ), 0 ≤ t →
    (1 + |t|) ^ K * ‖iteratedFDerivWithin ℝ N (fun z : E × ℝ => f z.1 z.2) S (x, t)‖ ≤ C

/-- "(1) ∂_t u_i + Σ_j u_j ∂_j u_i = ν Δ u_i − ∂_i p + f_i(x,t), for x ∈ ℝ^n, t ≥ 0."
∂_t is `derivWithin` on `Ici 0` (one-sided at t = 0), Δ u_i = Σ_j ∂_j ∂_j u_i.
Meaningful (no junk) when u, p are `SmoothOnS`, which is always conjoined where used. -/
def Eq1 (ν : ℝ) (u : E → ℝ → E) (p : E → ℝ → ℝ) (f : E → ℝ → E) : Prop :=
  ∀ (x : E) (t : ℝ), 0 ≤ t → ∀ i : Fin 3,
    derivWithin (fun s => u x s i) (Ici 0) t
      + ∑ j, u x t j * pd j (fun y => u y t i) x
    = ν * ∑ j, pd j (pd j (fun y => u y t i)) x - pd i (fun y => p y t) x + f x t i

/-- "(2) div u = Σ_i ∂_i u_i = 0, for x ∈ ℝ^n, t ≥ 0." -/
def Eq2 (u : E → ℝ → E) : Prop :=
  ∀ (x : E) (t : ℝ), 0 ≤ t → ∑ i, pd i (fun y => u y t i) x = 0

/-- "(3) u(x,0) = u°(x), for x ∈ ℝ^n." -/
def Eq3 (u : E → ℝ → E) (u0 : E → E) : Prop :=
  ∀ x, u x 0 = u0 x

/-- "(7) ∫_{ℝ^n} |u(x,t)|² dx < C for all t ≥ 0 (bounded energy)."
Integrability of |u(·,t)|² is required explicitly, so the Bochner integral is not a junk 0. -/
def Eq7 (u : E → ℝ → E) : Prop :=
  ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
    Integrable (fun x : E => ‖u x t‖ ^ 2) ∧ ∫ x : E, ‖u x t‖ ^ 2 < C

/-- "(8) u°(x + e_j) = u°(x)" (periodicity of the initial data). -/
def PerInit (u0 : E → E) : Prop :=
  ∀ (x : E) (j : Fin 3), u0 (x + e j) = u0 x

/-- "(8) f(x + e_j, t) = f(x,t)" (periodicity of the force, for t ≥ 0). -/
def PerForce (f : E → ℝ → E) : Prop :=
  ∀ (x : E) (t : ℝ), 0 ≤ t → ∀ j : Fin 3, f (x + e j) t = f x t

/-- "(10) u(x,t) = u(x + e_j, t) on ℝ³ × [0,∞), for 1 ≤ j ≤ n." -/
def Eq10 (u : E → ℝ → E) : Prop :=
  ∀ (x : E) (t : ℝ), 0 ≤ t → ∀ j : Fin 3, u x t = u (x + e j) t

/-- Errata: "The further condition p(x + e_j, t) = p(x, t) should be made explicit in Eqn (8)."
Imposed on the pressure of a periodic solution. -/
def PerPressure (p : E → ℝ → ℝ) : Prop :=
  ∀ (x : E) (t : ℝ), 0 ≤ t → ∀ j : Fin 3, p (x + e j) t = p x t

/-- Solution of (1), (2), (3), (6), (7) on ℝ³ × [0,∞). -/
def SolC (ν : ℝ) (u0 : E → E) (f : E → ℝ → E) (p : E → ℝ → ℝ) (u : E → ℝ → E) : Prop :=
  SmoothOnS p ∧ SmoothOnS u ∧ Eq1 ν u p f ∧ Eq2 u ∧ Eq3 u u0 ∧ Eq7 u

/-- Solution of (1), (2), (3), (10), (11) on ℝ³ × [0,∞) (plus periodic p per the errata). -/
def SolD (ν : ℝ) (u0 : E → E) (f : E → ℝ → E) (p : E → ℝ → ℝ) (u : E → ℝ → E) : Prop :=
  SmoothOnS p ∧ SmoothOnS u ∧ Eq1 ν u p f ∧ Eq2 u ∧ Eq3 u u0 ∧ Eq10 u ∧ PerPressure p

/-- (C) Breakdown of Navier–Stokes solutions on ℝ³. -/
theorem reading_C (ν : ℝ) (hν : 0 < ν) :
    ∃ (u0 : E → E) (f : E → ℝ → E),
      SmoothDivFree u0 ∧ SmoothOnS f ∧ Decay4 u0 ∧ Decay5 f ∧
      ¬ ∃ (p : E → ℝ → ℝ) (u : E → ℝ → E), SolC ν u0 f p u := by
  sorry

/-- (D) Breakdown of Navier–Stokes solutions on ℝ³/ℤ³. -/
theorem reading_D (ν : ℝ) (hν : 0 < ν) :
    ∃ (u0 : E → E) (f : E → ℝ → E),
      SmoothDivFree u0 ∧ SmoothOnS f ∧ PerInit u0 ∧ PerForce f ∧ Decay9 f ∧
      ¬ ∃ (p : E → ℝ → ℝ) (u : E → ℝ → E), SolD ν u0 f p u := by
  sorry

/-
AMBIGUITIES AND CHOICES

1. Junk values. Derivatives: every `fderiv`/`derivWithin`/`iteratedFDeriv(Within)` is applied to
   functions that are C^∞ (`SmoothOnS`/`ContDiff`): u, p are required smooth in every solution
   predicate, f and u° are required smooth in the theorem statements (u0 via `SmoothDivFree`,
   f via `SmoothOnS f`). Slices y ↦ u y t (t ≥ 0) are then smooth on all of E, and s ↦ u x s is
   smooth within Ici 0. Decay predicates are only asserted alongside smoothness. Integrals:
   `Eq7` requires `Integrable` of |u(·,t)|² before bounding the integral.
2. Smoothness on the closed set ℝ³ × [0,∞): read as `ContDiffOn ℝ ∞` on univ ×ˢ Ici 0
   (derivatives within the set, one-sided at t = 0), not as restriction of a smooth function on
   an open neighbourhood (these agree by Whitney-type extension, but not definitionally).
3. Functions are defined on all of E × ℝ (values at t < 0 irrelevant, never constrained).
4. Multi-index derivative bounds (4), (5), (9): replaced by Fréchet derivative norms of every
   total order (N for (x,t) jointly, k for x). Equivalent up to constants to all multi-indices.
   Bounds written as (weight)^K * ‖D‖ ≤ C with K : ℕ rather than with negative powers; the
   constant C depends on (order, K) only, not on x, t. K natural (not real) suffices.
5. (5) vs (4): the f-decay for ∂_x^α ∂_t^m uses joint derivatives within S, including m = 0.
   The bound in (9) is uniform in x ∈ ℝ³ (as written), decay only in t.
6. Quantifier structure of (C),(D): "there exist u° and f ... for which there exist no (p,u)":
   ∃ u0 f, (data hypotheses) ∧ ¬∃ p u, Solution. ν > 0 given (hν unused in the statement text,
   it is a hypothesis as in the brief; ν is fixed before the data).
7. (D) says the data are "on ℝ³", periodic via (8): I require u° and f smooth and periodic
   under all three unit translations e_j, and (9) for f. (4),(5) are NOT required in (D).
   Periodicity of f is only imposed for t ≥ 0.
8. (D) solution conditions: (1),(2),(3),(10),(11). The pressure periodicity (errata) is a
   judgment call; I include it in the solution notion `SolD`, which makes "no solution"
   a (weakly) easier claim than without it. Without it p could be periodic plus a linear
   function of x (with time-dependent coefficient).
9. (D) imposes no energy bound (7) (none applies on the torus: periodic u has infinite ℝ³ energy
   unless zero). (C) also omits periodicity.
10. (7): "< C for all t ≥ 0" read as ∃ C, ∀ t ≥ 0, ∫ < C (C independent of t); strict < as written.
11. The index range in (10) "1 ≤ j ≤ n" taken with n = 3, e_j = EuclideanSpace.single j 1.
12. (1) holds for t ≥ 0 including t = 0 with one-sided time derivative. The p in (1) enters only
    via its gradient. Δ is Σ_j ∂_j∂_j implemented by iterated `fderiv`.
13. Components: u x t j is the j-th coordinate of the vector u x t in EuclideanSpace ℝ (Fin 3);
    |·| is the Euclidean norm. Initial data u° : E → E is smooth on all of ℝ³ and div-free
    everywhere (also the compatibility div u(·,0) = 0 follows from (2),(3)).
14. The problem is the negation of the Clay existence/smoothness conjectures; no claim is made
    that (C) or (D) are true (they are the "breakdown" alternatives).
-/

end Reading
