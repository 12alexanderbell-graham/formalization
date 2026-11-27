# Blind reading brief: target O, families O35 "A counterexample to Kaplansky's direct finiteness conjecture in odd characteristic", O36 "A nine-dimensional counterexample to Borsuk's covering assertion", O37 "A counterexample to the infinite matroid packing/covering conjecture" (OpenAI release)

Committed before any reader runs. Readers A (Opus), B (Sonnet), C (Haiku), each alone, all three families.
You have NOT seen, and must not look for, any Lean formalization of these claims. Read exactly these files and
no others: this brief; `oddkaplansky/sources/introduction_lines1-22.tex` (01-introduction.tex sha256 prefix
726e3c3b8df888f7); `borsuk/sources/introduction_lines1-26.tex` (introduction.tex, 379065fa1a94dd7d);
`matroid/sources/introduction_lines1-114.tex` (01-introduction.tex, 8abfb85a2dfbd5cd). All paths are under
/home/claude/formalization/runs/2026-11-27T0628Z/O/. Do not list directories, do not use wildcards or globs in any
path, do not open anything else in the repository or under /home/claude/ext; no web. You may read Mathlib's source
(/home/claude/formalization/.lake/packages/mathlib) for names.

For each family write ONE Lean 4 file, `import Mathlib` only, at
/home/claude/formalization/runs/2026-11-27T0628Z/O/<family>/<your letter>/reading.lean, wrapped in
`namespace Reader<your letter>`, with every definition written by you from the source, and the claims as
`theorem reading… : … := sorry`, as literally as possible:
- O35 (oddkaplansky): Theorem 1.1 — with the source's m and p (do not evaluate them): p is an odd prime, and
  there are a field K of order p⁴, a finitely generated group G containing torsion, and a, b ∈ K[G] with ab = 1
  and ba ≠ 1. ("Specified" is informal: say how you treat it.)
- O36 (borsuk): Theorem 1.1 — X = {uuᵀ : ‖u‖ = 1} ⊂ {A ∈ Sym₄(ℝ) : tr A = 1} with the Frobenius metric, compact,
  of diameter √2, not coverable by ten subsets of diameter < √2; and, as a second theorem, "Borsuk's assertion fails
  in dimension nine" (some bounded set of positive diameter in ℝ⁹ cannot be covered by 10 subsets of smaller diameter).
- O37 (matroid): Theorem 1.1 (countably infinite E, two self-dual matroids on E with no independent covering
  I₀ ∪ I₁ = E and no packing/covering partition; use Mathlib's `Matroid`, which follows the infinite matroid
  axioms, and the source's definitions of restriction, contraction onto X, spanning, packing/covering partition);
  and Corollary 1.4 (the pair does not satisfy intersection), as theorems.
In a comment block below each file's code: every ambiguity and your choice. Avoid junk values and say how.
Check each file compiles: `cd /home/claude/formalization && export PATH=$HOME/.elan/bin:$PATH && lake env lean <file>`
(`sorry` only in the reading theorems).
