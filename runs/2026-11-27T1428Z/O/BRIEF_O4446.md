# Blind reading brief: target O, families O44 "Seymour's second-neighborhood conjecture", O45 "A counterexample to Kaplansky's zero-divisor conjecture", O46 "Uniformly bounded components of Gaussian-prime graphs" (OpenAI release)

Committed before any reader runs. Readers A (Opus), B (Sonnet), C (Haiku), each alone, all three families.
You have NOT seen, and must not look for, any Lean formalization of these claims. Read exactly these files and
no others: this brief; `seymour/sources/abstract_and_introduction_lines1-35.tex` (abstract + 00-introduction.tex
lines 1-35, sha256 prefix 827d72ffd88bdaff); `zerodiv/sources/abstract_and_introduction_lines44-57.tex` (paper.tex
lines 44-57, 39253fce0c4ab46d); `moat/sources/abstract_and_introduction_lines43-79.tex` (main.tex lines 43-79,
1a20979193bad4d8). All paths are under /home/claude/formalization/runs/2026-11-27T1428Z/O/. Do not list
directories (no `ls`), do not use wildcards or globs in any path, do not open anything else in the repository or
under /tmp; no web. You may read Mathlib's source (/home/claude/formalization/.lake/packages/mathlib) for names.
Macros: \abs{x} is |x|; \Z is the integers; \mathbb F_2 is the field with two elements.

For each family write ONE Lean 4 file, `import Mathlib` only, at
/home/claude/formalization/runs/2026-11-27T1428Z/O/<family>/<your letter>/reading.lean (create the directory with
`mkdir -p` of that exact path), wrapped in `namespace Reader<your letter>`, with every definition written by you
from the source (Mathlib's graph, group, group-algebra, topology and Gaussian-integer notions may be used), and
the claims as `theorem reading… : … := sorry`, as literally as possible:
- O44 (seymour): Theorem 1.1 (every nonempty finite oriented graph has a vertex v with |N₁⁺(v)| ≤ |N₂⁺(v)|, with
  N₁⁺ and N₂⁺ as the text defines them); and, as a second theorem, the directed-triangle consequence stated in the
  last paragraph of the excerpt, as literally as the sentence allows (say in the comment block how you read
  "at least one third of its order").
- O45 (zerodiv): Theorem 1.1 in full (a finitely presented torsion-free group G and nonzero α, β ∈ 𝔽₂[G] with
  αβ = 0), with its "Moreover" clause (G admits a finite two-dimensional classifying space) both as a separate
  theorem and conjoined with the first; and, as a third theorem, "Kaplansky's zero-divisor conjecture is false"
  as the introduction's first sentence states the conjecture (fields K, torsion-free G).
- O46 (moat): Theorem 1.1 (for every finite real D a finite B_D bounding the number of vertices of every connected
  component of G_D), its "Consequently" sentence (every sequence of distinct Gaussian primes with successive
  distances at most D has at most B_D terms) as a second theorem, and the answer to the infinite-walk question
  (no infinite path with no repeated vertex in any G_D) as a third.
In a comment block below each file's code: every ambiguity and your choice. Avoid junk values (ℕ subtraction,
x/0 = 0, Set.ncard of an infinite set = 0, sSup/sInf of empty or unbounded sets, ⊤ in ℕ∞-valued invariants)
and say how.
Check each file compiles: `cd /home/claude/formalization && export PATH=$HOME/.elan/bin:$PATH && lake env lean <file>`
(`sorry` only in the reading theorems). Reply with the three paths and a one-line summary each; do not commit.
