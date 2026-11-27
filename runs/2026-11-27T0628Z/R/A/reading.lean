import Mathlib

/-!
# Blind reading A: the RH / GRH claim in Alpöge's note (2026-11-20)

Written from the brief and the pdftotext of `remark.pdf` only.
-/

open Complex

/-- The Riemann Hypothesis: every nontrivial zero of `ζ` has real part `1/2`.

"Nontrivial" is read literally as "not one of the trivial zeros `-2, -4, -6, …`".
The point `s = 1` (the pole, where Mathlib's `riemannZeta` takes a junk value) is
excluded explicitly, so the statement never depends on that junk value. -/
def ReadingRH : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 →
    (∀ n : ℕ, s ≠ -2 * ((n : ℂ) + 1)) →
    s ≠ 1 →
    s.re = 1 / 2

/-- Second, equally standard phrasing of RH (not requested, recorded for comparison):
every zero of `ζ` in the critical strip `0 < Re s < 1` lies on `Re s = 1/2`.
The pole `s = 1` has `Re s = 1`, so it is outside the strip automatically. -/
def ReadingRH_strip : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1 / 2

/-- GRH for Dirichlet L-functions, main reading: for every modulus `N ≥ 1` and EVERY
Dirichlet character `χ` mod `N` (primitive or not, principal or not), every zero of
`L(s, χ)` in the critical strip `0 < Re s < 1` has real part `1/2`.

Using the open strip is what makes "all characters" correct: an imprimitive `χ` has
extra zeros on `Re s = 0` coming from the Euler factors `1 - χ*(p) p^{-s}` (`p ∣ N`,
`χ*` the primitive character inducing `χ`), and these are not counted by GRH.
The pole of the principal character is at `s = 1`, which has `Re s = 1`, so it is
outside the strip and the statement never reads the junk value there.
`N = 0` is excluded (`NeZero N`), as Mathlib's `LFunction` requires and as there are
no Dirichlet characters "mod 0" in the number-theoretic sense. -/
def ReadingGRH : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

/-- GRH for Dirichlet L-functions, second reading: for every PRIMITIVE Dirichlet
character `χ` mod `N ≥ 1`, every nontrivial zero of `L(s, χ)` has real part `1/2`,
where the trivial zeros are those of the gamma factor:
* `χ` even (`χ (-1) = 1`): `s = 0, -2, -4, …`;
* `χ` odd  (`χ (-1) = -1`): `s = -1, -3, -5, …`.
(For `N = 1`, `χ = 1`, `L = ζ`; `s = 0` is not actually a zero of `ζ`, so excluding it
is harmless.) The point `s = 1` is excluded for every `χ`: it is the pole when `χ` is
trivial (only `N = 1` among primitive characters), and for nontrivial `χ` it is not a
zero (`L(1, χ) ≠ 0`), so the exclusion costs nothing and avoids the junk value. -/
def ReadingGRH' : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 →
      ¬ ((χ (-1) = 1 ∧ ∃ n : ℕ, s = -(2 * (n : ℂ))) ∨
         (χ (-1) = -1 ∧ ∃ n : ℕ, s = -(2 * (n : ℂ) + 1))) →
      s ≠ 1 →
      s.re = 1 / 2

/-
## Ambiguity notes (reader A)

1. The note states no theorem. Page 1: "discovered a proof of the Riemann Hypothesis ...
   resolving the so-called Generalized Riemann Hypothesis"; page 4, item 20: "11/16/26: GRH."
   No precise statement, no list of L-functions, no definition of "nontrivial zero".

2. RH, meaning of "nontrivial zero". Two standard readings:
   (a) zeros other than the trivial zeros -2, -4, ... (`ReadingRH`, chosen as the
       literal textbook statement); (b) zeros in the critical strip 0 < Re s < 1
       (`ReadingRH_strip`). They are equivalent given classical facts (ζ ≠ 0 on Re s ≥ 1,
       functional equation, ζ(0) = -1/2), but not definitionally; (a) is formally the
       stronger-looking one because it also asserts there are no zeros with Re s ≤ 0
       other than the trivial ones.

3. RH, the pole s = 1. Mathlib's `riemannZeta 1` is a junk value (I believe it is
   (γ - log 4π)/2, which is nonzero, so the hypothesis `s ≠ 1` should be redundant),
   but I exclude s = 1 explicitly so the statement does not depend on that junk value.

4. RH, trivial zeros indexed by `n : ℕ` as `-2(n+1)` with complex arithmetic: no ℕ
   subtraction, no division by a possibly-zero term (only the literal `1/2` in ℝ).

5. GRH, scope of the word. As instructed, I formalized GRH for Dirichlet L-functions.
   The word is also commonly used for: Dedekind zeta functions of number fields
   (often called ERH, "Extended RH"; the note says ERH is only *expected*, "with more
   time", which suggests the author uses GRH = Dirichlet L-functions and
   ERH = Dedekind zeta / Hecke L-functions); Hecke L-functions of Grössencharacters;
   Artin L-functions; or all automorphic L-functions on GL(n) ("Grand RH"). Note that
   the timeline mentions "Hecke characters" (items 12, 15), so the method may touch
   Hecke L-functions, but nothing states that the result covers them.

6. GRH, which characters. (a) all Dirichlet characters, zeros in the open critical strip
   (`ReadingGRH`, chosen as main reading: it is the most common textbook phrasing and is
   robust to imprimitive characters and to the principal character's pole);
   (b) primitive characters only, all non-trivial zeros (`ReadingGRH'`). These are
   equivalent given classical facts (every χ is induced by a primitive χ*, the Euler
   factors at p | N do not vanish for 0 < Re s < 1, L(s, χ*) ≠ 0 on Re s ≥ 1, and the
   functional equation), but not definitionally. The reading "all characters, all
   zeros off the trivial ones" would be FALSE for imprimitive χ (zeros on Re s = 0
   from Euler factors), so it is not a sensible reading and is not formalized.

7. GRH, trivial zeros for primitive χ depend on parity: s = -2n (n ≥ 0) for even χ,
   s = -(2n+1) for odd χ. I write parity as `χ (-1) = 1` / `χ (-1) = -1` directly
   instead of relying on a Mathlib name. For N = 1 or 2, `-1 = 1` in `ZMod N`, so χ is
   even, which is correct.

8. GRH, the pole. Only the principal character has a pole (at s = 1). In `ReadingGRH`
   s = 1 lies outside the open strip; in `ReadingGRH'` it is excluded for all χ, which is
   harmless since L(1, χ) ≠ 0 for χ ≠ 1.

9. GRH, the modulus N = 0. `DirichletCharacter ℂ 0` exists in Mathlib (characters of
   (ℤ)ˣ) but `LFunction` needs `[NeZero N]`; I quantify only over N with `NeZero N`.

10. Whether Mathlib's `DirichletCharacter.LFunction χ` for imprimitive χ is the
    continuation of Σ χ(n) n^{-s} (with the Euler factors) rather than L(s, χ*): I assume
    the former (it is what I recall); `ReadingGRH` is correct under either convention.

11. "formalized the arguments without assumptions": unclear whether that means no
    `sorry`/axioms beyond Lean's standard ones, or no unproved hypotheses in the final
    theorem. Not something a statement can capture; noted only.

## Other claims in the note stated as proved / done (quoted)

- Formalization: "Claude and I have also formalized the arguments without assumptions."
  and "while its formalization is finished and it is routine to produce a huge, unreadable
  document containing sufficient detail".
- A complete argument: "I am presenting the world with a complete argument before having
  mastered a massive neighbourhood around its mathematics."
- A new proof of the Weil conjectures / Deligne: "when I had the qN = M k + R sign-only
  proof of Weil and Deligne." (stated as something the author had).
- Size: footnote 2, "I of course amused myself, and hit 250, 000+ pages."
- Timeline items stated as achieved (not theorems with statements), e.g.
  item 2 "Dp ≡ 0 on a CM curve for p inert in K ... is divisible by ...";
  item 4 "W (1S ) ≥ 0 via a determinant";
  item 6 "W 1(0,1] + (∼ X η ) · 1(0,1/X] ≥ 0 gives > 1 − η." (reads like a proportion-of-
  zeros-on-the-line bound > 1 − η, but this is my guess);
  item 8 "Iterated theta lifts ... wins multiplicity m";
  item 9 "... cancellation of order-m terms with proven divisibility via Chowla-Selberg,
  Weyl, and Siegel mass.";
  item 10 "Sufficient lower bound on divisibility of the m-fold iterated lift.";
  item 14 "precise computation of the "cost" of each lift, showing that one would stop at
  2/3 a priori";
  item 17 "fight for a significant weakening of Vandiver." with footnote 6 "This is still
  pretty strong!! I believe vanishing of a number of K-groups of Z follows" (stated as a
  belief, not as proved).
- NOT claimed as proved by the author: ERH ("I expect, with more time, the Extended Riemann
  Hypothesis too"); Navier-Stokes ("immediately understood Navier-Stokes was going to
  fall", about others' work); the Ehrhart conjecture (attributed to OpenAI).
-/
