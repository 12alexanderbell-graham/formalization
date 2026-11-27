# Blind reading brief: target O, families O41 "A counterexample to Hadwiger's conjecture", O42 "A linear list-coloring bound in terms of the Hadwiger number", O43 "Rokhlin's multiple-mixing problem for one transformation" (OpenAI release)

Committed before any reader runs. Readers A (Opus), B (Sonnet), C (Haiku), each alone, all three families.
You have NOT seen, and must not look for, any Lean formalization of these claims. Read exactly these files and
no others: this brief; `hadwiger/sources/abstract_and_introduction_lines1-60.tex` (abstract + 01-introduction.tex
lines 1-60, sha256 prefix 69c36e38f69ac089); `listhadwiger/sources/abstract_and_introduction_lines1-45.tex`
(ce4c975c0c6bba91); `rokhlin/sources/abstract_and_introduction_lines1-40.tex` (88914bccc2fac68b). All paths are
under /home/claude/formalization/runs/2026-11-27T1317Z/O/. Do not list directories (no `ls`), do not use wildcards
or globs in any path, do not open anything else in the repository or under /tmp; no web. You may read Mathlib's
source (/home/claude/formalization/.lake/packages/mathlib) for names. Macros: \cm is the connected-matching number
cm(G); \chi_f is the fractional chromatic number.

For each family write ONE Lean 4 file, `import Mathlib` only, at
/home/claude/formalization/runs/2026-11-27T1317Z/O/<family>/<your letter>/reading.lean (create the directory with
`mkdir -p` of that exact path), wrapped in `namespace Reader<your letter>`, with every definition written by you
from the source (Mathlib's graph, coloring, measure notions may be used), and the claims as
`theorem reading… : … := sorry`, as literally as possible:
- O41 (hadwiger): Theorem 1.1 (arbitrarily large m with an m-vertex graph, α(G) ≤ 2 and cm(G) < m/100);
  Corollary 1.2 (arbitrarily large order m with h(G) < 26m/75 + 2/3 < m/2 ≤ χ_f(G) ≤ χ(G)); and "Hadwiger's
  conjecture is false" (not every finite nonempty simple graph has h(G) ≥ χ(G)) as a third theorem. Define the
  Hadwiger number, connected matchings and χ_f yourself from the text.
- O42 (listhadwiger): Theorem 1.1 (an absolute integer C ≥ 1 with ℓ(G) ≤ C·h(G) for every finite nonempty simple
  graph) and Corollary 1.2 (χ(G) ≤ C·h(G) with the same C).
- O43 (rokhlin): Theorem 1.1 in its explicit form (invertible, measurable inverse, probability-preserving, mixing ⇒
  for every k ≥ 3 and measurable A₁…A_k the displayed limit as min(n₁,…,n_{k−1}) → ∞ through positive integers),
  and the definition-level form "mixing of order k for every k ≥ 2" (with t₁ < … < t_k integers) as a second theorem.
In a comment block below each file's code: every ambiguity and your choice. Avoid junk values (ℕ subtraction,
x/0 = 0, sSup/sInf of empty or unbounded sets, ⊤ in ℕ∞-valued invariants) and say how.
Check each file compiles: `cd /home/claude/formalization && export PATH=$HOME/.elan/bin:$PATH && lake env lean <file>`
(`sorry` only in the reading theorems). Reply with the three paths and a one-line summary each; do not commit.
