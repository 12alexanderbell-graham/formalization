# Blind reading brief: target O, families O38 "Fixed points of nonexpansive maps in reflexive Banach spaces", O39 "Pure-point spectrum for the two-dimensional Anderson model at every positive disorder", O40 "Quasipolynomial bounds for arithmetic progressions" (OpenAI release)

Committed before any reader runs. Readers A (Opus), B (Sonnet), C (Haiku), each alone, all three families.
You have NOT seen, and must not look for, any Lean formalization of these claims. Read exactly these files and
no others: this brief; `fixedpoint/sources/abstract_and_introduction_lines1-40.tex` (abstract + 00-introduction.tex
lines 1-40, sha256 prefix ebea2fdb68775475); `anderson/sources/introduction_lines1-40.tex` (introduction.tex,
8556210d7d0d039d); `erdosap/sources/introduction_lines1-60.tex` (00-introduction.tex, 20254cf37d610fb7). All paths
are under /home/claude/formalization/runs/2026-11-27T1317Z/O/. Do not list directories, do not use wildcards or globs
in any path, do not open anything else in the repository or under /tmp; no web. You may read Mathlib's source
(/home/claude/formalization/.lake/packages/mathlib) for names. Macros: \R, \N, \Z are ℝ, ℕ, ℤ; \norm{x} is ‖x‖;
\abs{x} is |x|.

For each family write ONE Lean 4 file, `import Mathlib` only, at
/home/claude/formalization/runs/2026-11-27T1317Z/O/<family>/<your letter>/reading.lean, wrapped in
`namespace Reader<your letter>`, with every definition written by you from the source (Mathlib's general notions —
normed spaces, the bidual, ℓ², spectrum, measures — may be used), and the claims as
`theorem reading… : … := sorry`, as literally as possible:
- O38 (fixedpoint): Theorem 1.1 (real reflexive Banach space X; C nonempty, norm closed, bounded, convex;
  F : C → C nonexpansive in the given norm ⇒ F has a fixed point), and Corollary 1.2 (commuting families: the common
  fixed set is nonempty and a nonexpansive retract of C) as a second theorem. Say how you define "reflexive".
- O39 (anderson): Theorem 1.1, every conclusion separately: for each h > 0, almost surely (v_x iid uniform on
  [−h, h]) H_v (i) has spectrum [−4−h, 4+h], (ii) has pure-point spectral type (closed span of eigenvectors is all
  of ℓ²(ℤ²)), (iii) admits a complete orthonormal eigenbasis, (iv) its eigenvalues are dense in [−4−h, 4+h].
- O40 (erdosap): Theorem 1.1 (the density bound for r_k(N), k ≥ 3, N ≥ 2, with the source's definition of r_k(N)),
  its "Equivalently" threshold form as a second theorem, and Corollary 1.2 (divergent reciprocal sums ⇒ nonconstant
  progressions of every finite length) as a third.
In a comment block below each file's code: every ambiguity and your choice. Avoid junk values (ℕ subtraction,
x/0 = 0, 1/0 for a ∈ A, log of small numbers, sSup ∅) and say how.
Check each file compiles: `cd /home/claude/formalization && export PATH=$HOME/.elan/bin:$PATH && lake env lean <file>`
(`sorry` only in the reading theorems). Reply with the three paths and a one-line summary each; do not commit.
