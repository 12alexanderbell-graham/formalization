import Mathlib

/-- Riemann Hypothesis: every zero of ζ in the open critical strip 0 < Re s < 1
has real part 1/2. -/
def ReadingRH : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1 / 2

/-- GRH for Dirichlet L-functions: for every modulus N ≥ 1 and every primitive
Dirichlet character χ mod N, every zero of L(χ, ·) in the open strip 0 < Re s < 1
has real part 1/2. -/
def ReadingGRH : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

/-- Second reading: all Dirichlet characters (primitive or not), zeros in the
open strip 0 < Re s < 1. -/
def ReadingGRH' : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
    ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

/-
AMBIGUITY NOTES (reader B)

1. "Nontrivial zero" of zeta. Standard: zeros other than -2, -4, -6, ...; all lie in
   0 < Re s < 1. I used the open strip 0 < Re s < 1 as the definition. Reason: it avoids
   mentioning the trivial zeros and avoids s = 1 (Re = 1, excluded) where Mathlib's
   riemannZeta has a junk value. Equivalent to the textbook statement (zeta has no zeros
   with Re >= 1 and the only zeros with Re <= 0 are the trivial ones), but that
   equivalence uses known theorems; the strip form is the common formulation.
2. GRH, which characters. ReadingGRH: primitive characters of every modulus N >= 1
   (N = 1 gives zeta itself, so GRH implies RH). ReadingGRH': all characters. In the open
   strip the two are equivalent mathematically (an imprimitive L-function is the
   primitive one times a finite Euler factor product whose extra zeros lie on Re s = 0),
   so I used the open strip, NOT the closed strip, for ReadingGRH' (the closed strip
   would be false for imprimitive characters). Principal character pole at s = 1 is
   excluded by Re s < 1, so no junk value is used.
3. Zeros: "nontrivial" for L(chi,s): zeros of primitive L lie trivially at certain
   nonpositive integers (Re <= 0); strip zeros are the nontrivial ones. Same convention.
4. Broader meaning of "GRH": could also mean Dedekind zeta functions / Hecke L-functions
   of number fields, Artin L-functions, or automorphic L-functions (Selberg class,
   zeros on Re s = 1/2 in the analytic normalization). The note itself names "Extended
   Riemann Hypothesis" separately (Dedekind/number-field zeta, as it is sometimes
   used), so GRH here is read as Dirichlet; terminology varies by author.
5. The note states no theorem formally; "Theorem 1 ... if sigma != 1/2 then sigma > 1/2
   or sigma < 1/2" suggests a proof by contradiction on a zero rho = sigma + i t, not
   fixing a precise statement. Whether the Lean archive's statement matches is unchecked.
6. Other claims stated as proved in the note:
   - "Claude and I have also formalized the arguments without assumptions."
   - "I believe I have, working with Claude, discovered a proof of the Riemann Hypothesis."
   - "while its formalization is finished and it is routine to produce a huge, unreadable
     document containing sufficient detail".
   - "resolving the so-called Generalized Riemann Hypothesis" (and "I expect, with more
     time, the Extended Riemann Hypothesis too": expectation only, not claimed proved).
   - Timeline item 20: "11/16/26: GRH."
   - Footnote 6 is a belief: "I believe vanishing of a number of K-groups of Z follows".
   - "I immediately recognized ... Navier-Stokes was going to fall" (a prediction).
-/
