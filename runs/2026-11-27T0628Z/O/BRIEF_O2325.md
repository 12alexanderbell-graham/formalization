# Blind reading brief: target O, families O23 "A quadratic bound for Jacobsthal's function", O24 "Single-fold Diophantine representations", O25 "A single lattice covering bound of order n log n" (OpenAI release)

Committed before any reader runs. Readers A (Opus), B (Sonnet), C (Haiku), each alone, all three families.
You have NOT seen, and must not look for, any Lean formalization of these claims. Read exactly these files and
no others: this brief; `jacobsthal/sources/introduction_lines1-35.tex` (introduction.tex sha256 prefix
94390edea0aecf1a); `singlefold/sources/main_lines42-132.tex` (main.tex, 1872e660edacb24a);
`latticecov/sources/overview_lines1-25.tex` (overview.tex, 99f45ea78f7a1a62). All paths are under
/home/claude/formalization/runs/2026-11-27T0628Z/O/. Do not list directories, do not use wildcards or globs in any
path, do not open anything else in the repository or under /home/claude/ext; no web. You may read Mathlib's source
(/home/claude/formalization/.lake/packages/mathlib) for names.

For each family write ONE Lean 4 file, `import Mathlib` only, at
/home/claude/formalization/runs/2026-11-27T0628Z/O/<family>/<your letter>/reading.lean, wrapped in
`namespace Reader<your letter>`, with every definition written by you from the source, and the claims as
`theorem reading… : … := sorry`, as literally as possible:
- O23 (jacobsthal): Theorem 1.1 with the source's j(n), ω(n) and h(k) = sup_{ω(n) ≤ k} j(n); and, as a second
  theorem, the weaker statement the text says it answers (Jacobsthal's question h(k) ≪ k²).
- O24 (singlefold): Theorem 1.1 (every recursively enumerable S ⊆ ℕⁿ, n ≥ 1, has a polynomial P over ℤ in
  A₁…Aₙ, W₁…W_m, m ≥ 1, with exactly one w ∈ ℕ^m with P(a, w) = 0 when a ∈ S and none otherwise); and the
  Corollary (undecidability with an at-most-one-solution promise). Use Mathlib's notions of computability as you
  judge closest to the source, and say why.
- O25 (latticecov): Theorem 1.1 (an absolute C > 0 such that for every n ≥ 2 and every convex body K ⊂ ℝⁿ some
  full-rank lattice Λ has K + Λ = ℝⁿ and vol(K)/det Λ ≤ C n log n).
In a comment block below each file's code: every ambiguity and your choice. Avoid junk values (`sSup` of an
unbounded or empty set, `log` of small arguments, ℕ subtraction, `toReal` of ∞, …) and say how.
Check each file compiles: `cd /home/claude/formalization && export PATH=$HOME/.elan/bin:$PATH && lake env lean <file>`
(`sorry` only in the reading theorems).
