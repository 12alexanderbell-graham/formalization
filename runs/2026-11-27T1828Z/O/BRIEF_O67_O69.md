# Blind reading brief: target O, O67 "Counterexamples to Sidorenko's conjecture and the forcing conjecture", O68 "Barnette's Hamiltonian-cycle conjecture", O69 "Smooth isometric immersions of surfaces into R^4" (OpenAI release)

Committed before any reader runs. Readers A (Opus), B (Sonnet), C (Haiku), each alone, all three families.
You have NOT seen, and must not look for, any Lean formalization of these claims. Read exactly these files and
no others: this brief; `sidorenko/sources/excerpts.tex` (abstract, introduction lines 1-26 and 279-345, and the
table of faces from complex.tex, as marked inside; sha256 prefix 16e5b5fedf0009b7); `barnette/sources/excerpts.tex`
(abstract and introduction up to the main theorem, 0df57687ba6002dd); `immersion/sources/excerpts.tex` (abstract and
introduction lines 1-22, aa5edd24d5edc4f6). All paths are under
/home/claude/formalization/runs/2026-11-27T1828Z/O/. Do not list directories (no `ls`), do not use wildcards or
globs in any path, do not open anything else in the repository or under /tmp or /home/claude/ext; no web. You may
read Mathlib's source (/home/claude/formalization/.lake/packages/mathlib) for names: search it with the Grep tool
(a Bash `grep` may be refused). Macros: \R the reals, \E expectation, \P probability, \F a finite field, \1 an
indicator, \Hom the number of homomorphisms; \cite, \Cref, \eqref, \ref are references.

Write each file at exactly /home/claude/formalization/runs/2026-11-27T1828Z/O/<family>/<your letter>/reading.lean,
where <family> is one of the three words `sidorenko`, `barnette`, `immersion` (create the directory with `mkdir -p`
of that exact path). One Lean 4 file per family, `import Mathlib` only, wrapped in `namespace Reader<your letter>`,
with every definition written by you from the source (Mathlib's complex-analysis, integration, filter, convex
geometry, measure, finite-type and relation notions may be used), and the claims as
`theorem reading… : … := sorry`, as literally as possible:
- O67 (sidorenko): Theorem 1.1 (H the incidence graph of the 22 triples of the table, its vertex and edge counts,
  and the existence of G with t(H,G) < p(G)^66; t and p as the text defines them, Hom counting all maps) and the two
  corollaries in the excerpt, as literally as possible (write the table into Lean as data).
- O68 (barnette): Theorem 1.1 (finite simple undirected graphs, cubic, bipartite, planar, 3-vertex-connected,
  Hamiltonian cycle; write planarity yourself if Mathlib has no usable notion, and say how).
- O69 (immersion): Theorem 1.1 (closed smooth surface, possibly nonorientable or disconnected, smooth Riemannian
  metric, C^∞ isometric immersion into R^4 with the Euclidean metric; Mathlib manifolds may be used).
In a comment block below each file's code: every ambiguity and your choice. Avoid junk values (ℕ subtraction,
x/0 = 0, sSup/sInf/iSup/iInf of empty or unbounded sets, `Real.log` of non-positive numbers, `Real.rpow` of
negative bases, `deriv` of non-differentiable functions, integrals of non-integrable functions (`∫` is 0 then),
⊤/⊥ in extended quantities) and say how. Write no decimals or fractions in a `/-! -/` module doc.
Check each file compiles: `cd /home/claude/formalization && export PATH=$HOME/.elan/bin:$PATH && lake env lean <file>`
(`sorry` only in the reading theorems; allow a few minutes per compile). If a notion has no usable Mathlib
counterpart, define it yourself from the text, or state in the comment block exactly which part you could not
write and why. Reply with the three paths and a one-line summary each; do not commit.
