# Blind reading brief: target O, families O20 "The symmetric Mahler conjecture and its equality cases", O21 "A classification of finite Euclidean Ramsey configurations", O22 "The circulant Hadamard conjecture" (OpenAI release)

Committed before any reader runs. Readers A (Opus), B (Sonnet), C (Haiku), each alone, all three families.
You have NOT seen, and must not look for, any Lean formalization of these claims. Read exactly these files and
no others: this brief; `mahler/sources/introduction_lines1-44.tex` (introduction.tex sha256 prefix
64a324e85b52d070); `ramsey/sources/introduction_lines1-116.tex` (01-introduction.tex, 55d8307a438125cd);
`hadamard/sources/introduction_lines1-49.tex` (introduction.tex, 54c2d276b2e90a0e). All paths are under
/home/claude/formalization/runs/2026-11-27T0628Z/O/. Do not list directories, do not use wildcards or globs in any
path, do not open anything else in the repository or under /home/claude/ext; no web. You may read Mathlib's source
(/home/claude/formalization/.lake/packages/mathlib) for names.

For each family write ONE Lean 4 file, `import Mathlib` only, at
/home/claude/formalization/runs/2026-11-27T0628Z/O/<family>/<your letter>/reading.lean, wrapped in
`namespace Reader<your letter>`, with every definition written by you from the source, and the claims as
`theorem reading… : … := sorry`, as literally as possible:
- O20 (mahler): Theorem 1.1 — the inequality |K||K°| ≥ 4^n/n! for every n ≥ 1 and every origin-symmetric convex
  body K ⊂ ℝⁿ (one theorem), and the equality case (a second theorem: equality iff K is a linear Hanner body,
  with Hanner polytopes defined recursively as in the source).
- O21 (ramsey): the definition of a Ramsey set (first paragraph) as literally as possible; the Classification theorem
  — if Mathlib's tensor products make it too costly, state it as literally as you can and say
  precisely what you changed; and the three consequences stated in prose in the excerpt, each as its own theorem:
  (i) every subtransitive set (an isometric copy of a subset of a finite set whose isometry group acts
  transitively) is Ramsey; (ii) every nonempty set of at most five points on a circle is Ramsey; (iii) the
  classical necessity cited in the second paragraph: every finite Ramsey set is spherical.
- O22 (hadamard): Theorem 1.1 (for n > 0, a real circulant Hadamard matrix of order n exists iff n ∈ {1, 4});
  and Corollary 1.2 (for n > 1, a Barker sequence of length n exists iff n ∈ {2, 3, 4, 5, 7, 11, 13}).
In a comment block below each file's code: every ambiguity and your choice. Avoid junk values (ℕ subtraction,
`Fin` wrap-around, measure `toReal` of an infinite measure, …) and say how.
Check each file compiles: `cd /home/claude/formalization && export PATH=$HOME/.elan/bin:$PATH && lake env lean <file>`
(`sorry` only in the reading theorems).
