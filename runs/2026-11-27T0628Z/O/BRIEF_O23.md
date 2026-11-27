# Blind reading brief: target O, families O2 "Catalan's constant is irrational" and O3 "A Counterexample to Kaplansky's Direct-Finiteness Conjecture in Characteristic Two" (OpenAI release)

Committed before any reader runs. Readers A (Opus), B (Sonnet), C (Haiku), each alone, both families.
You have NOT seen, and must not look for, any Lean formalization of these claims. Read only this brief and
the files in `catalan/sources/` and `kaplansky2/sources/` (verbatim TeX lines; Catalan introduction.tex
sha256 dfef42bb…9e80; Kaplansky 01-introduction.tex sha256 4abc0e82…e5de6). No other file, no web.
You may read Mathlib's source (/home/claude/formalization/.lake/packages/mathlib) for names.

For each family write ONE Lean 4 file, `import Mathlib` only, at `<family>/<your letter>/reading.lean`:

O2 (catalan): `def CatalanConstant : ℝ` from the source's definition (say why your series converges and
that Lean's `tsum` is not a junk 0 for it), and `theorem reading : Irrational CatalanConstant := sorry`.
If the source gives a second equivalent definition (β(2), L(2, χ₋₄)), add `theorem reading_alt` for it.

O3 (kaplansky2): `theorem reading : <Theorem 1.1 as literally as possible> := sorry` (finite field of
characteristic two; finitely presented group containing an element of odd prime order; elements of the
group algebra K[G] with ab = 1 and ba ≠ 1). Use Mathlib's group algebra (`MonoidAlgebra K G`) and
`Group.IsFinitelyPresented` if they exist; say what you used. Also `theorem reading_gottschalk` for the
cellular-automaton consequence stated in the source (lines 45–52), as literally as you can (define
cellular automata on A^G, injective, surjective yourself if Mathlib lacks them). Say which claims are
stated as proved and which only as consequences.

In a comment block below each file's code: every ambiguity and your choice. Avoid junk values. Check each
file compiles: `cd /home/claude/formalization && export PATH=$HOME/.elan/bin:$PATH && lake env lean <file>`
(`sorry` only in the theorems).
