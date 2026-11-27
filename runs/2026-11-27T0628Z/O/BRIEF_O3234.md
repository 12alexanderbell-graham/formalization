# Blind reading brief: target O, families O32 "Finite algebraic envelopes and the Boone–Higman conjecture", O33 "An explicit failure of complex affine space cancellation", O34 "Bi-Lipschitz absorption of c₀ without a linear copy of c₀" (OpenAI release)

Committed before any reader runs. Readers A (Opus), B (Sonnet), C (Haiku), each alone, all three families.
You have NOT seen, and must not look for, any Lean formalization of these claims. Read exactly these files and
no others: this brief; `boonehigman/sources/introduction_lines1-20.tex` (introduction.tex sha256 prefix
48b6881593433a17); `cancellation/sources/introduction_lines1-96.tex` (01-introduction.tex, 735089761fe623a3);
`c0absorb/sources/introduction_lines1-57.tex` (01-introduction.tex, 13bfea3a71b03773). All paths are under
/home/claude/formalization/runs/2026-11-27T0628Z/O/. Do not list directories, do not use wildcards or globs in any
path, do not open anything else in the repository or under /home/claude/ext; no web. You may read Mathlib's source
(/home/claude/formalization/.lake/packages/mathlib) for names.

For each family write ONE Lean 4 file, `import Mathlib` only, at
/home/claude/formalization/runs/2026-11-27T0628Z/O/<family>/<your letter>/reading.lean, wrapped in
`namespace Reader<your letter>`, with every definition written by you from the source, and the claims as
`theorem reading… : … := sorry`, as literally as possible:
- O32 (boonehigman): Theorem 1.1 — for every finitely generated group G, decidable word problem ⇔ G embeds in a
  finitely presented simple group (use the source's definitions of decidable word problem and simple; choose
  Mathlib's computability notions as you judge closest and say why).
- O33 (cancellation): Theorem 1.1 for the explicit A = ℂ[p,s,u,F,J]/(H) — integral, dimension four, A[w] ≅ ℂ[5
  variables], A ≇ ℂ[4 variables] (isomorphisms of ℂ-algebras); and Corollary 1.2 (H is not a coordinate of P but
  is a coordinate of P[w]; define "coordinate" as you judge the source means — say so).
- O34 (c0absorb): Theorem 1.1 — a separable real Banach space Z with no closed linear subspace isomorphic to c₀,
  and an onto bi-Lipschitz map Z ⊕_∞ c₀ → Z (c₀ = real sequences tending to zero, sup norm).
In a comment block below each file's code: every ambiguity and your choice. Avoid junk values and say how.
Check each file compiles: `cd /home/claude/formalization && export PATH=$HOME/.elan/bin:$PATH && lake env lean <file>`
(`sorry` only in the reading theorems).
