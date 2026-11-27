# Blind reading brief: target O, families O11 "A Logarithmic Independence Bound for Clique-Free Graphs" and O13 "An Infinite Finitely Presented Simple Amenable Group" (OpenAI release)

Committed before any reader runs. Readers A (Opus), B (Sonnet), C (Haiku), each alone, both families.
(O12, the seven-coloring of the plane, is the second Lean statement of family O4 and needs no reading.)
You have NOT seen, and must not look for, any Lean formalization of these claims. Read only this brief and the
files in `cliquefree/sources/` and `amenable/sources/` (verbatim TeX; sha256 prefixes: clique-free
introduction.tex 8fc8936de587ee76, amenable introduction.tex a8b988e030edf9ac). Do not open or list any other
file or directory of the repository (no globs over runs/) or under /home/claude/ext; no web. You may read
Mathlib's source (/home/claude/formalization/.lake/packages/mathlib) for names.

For each family write ONE Lean 4 file, `import Mathlib` only, at `<family>/<your letter>/reading.lean`,
with every definition the claim needs written by you from the source (amenability as the source defines it),
and the headline theorem as `theorem reading : … := sorry`, as literally as possible:
- O11 (cliquefree): Theorem 1.1 (every r ≥ 4, a constant c_r > 0, every finite K_r-free graph with n
  vertices and average degree d ≥ 2 has independence number ≥ c_r n log d / d).
- O13 (amenable): Theorem 1.1 (there exists an infinite finitely presented simple amenable group).
In a comment block below each file's code: every ambiguity and your choice. Avoid junk values (log of
non-positive, division by zero, `sSup`/`sInf` junk) and say how. Check each file compiles:
`cd /home/claude/formalization && export PATH=$HOME/.elan/bin:$PATH && lake env lean <file>`.
