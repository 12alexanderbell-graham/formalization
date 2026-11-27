# Blind reading brief: target O, families O26 "The Euclidean Steinitz–Bergström theorem", O27 "A doubling Hilbert subset with no finite-dimensional bi-Lipschitz embedding", O28 "Uniform exclusion of Landau–Siegel zeros" (OpenAI release)

Committed before any reader runs. Readers A (Opus), B (Sonnet), C (Haiku), each alone, all three families.
You have NOT seen, and must not look for, any Lean formalization of these claims. Read exactly these files and
no others: this brief; `steinitz/sources/introduction_lines1-45.tex` (introduction.tex sha256 prefix
84a36d95262ffd06); `doubling/sources/main_lines31-53.tex` (main.tex, 3eac74d00462787a);
`siegel/sources/paper_lines49-73.tex` (paper.tex, b011ba9c1f55ee21). All paths are under
/home/claude/formalization/runs/2026-11-27T0628Z/O/. Do not list directories, do not use wildcards or globs in any
path, do not open anything else in the repository or under /home/claude/ext; no web. You may read Mathlib's source
(/home/claude/formalization/.lake/packages/mathlib) for names.

For each family write ONE Lean 4 file, `import Mathlib` only, at
/home/claude/formalization/runs/2026-11-27T0628Z/O/<family>/<your letter>/reading.lean, wrapped in
`namespace Reader<your letter>`, with every definition written by you from the source, and the claims as
`theorem reading… : … := sorry`, as literally as possible:
- O26 (steinitz): Theorem 1.1 (prescribed-order signed prefixes) and Theorem 1.2 (Euclidean Steinitz–Bergström
  bound), each its own theorem; and, if you can state it, "the constant in Theorem 1.1 also suffices here" (one
  C for both).
- O27 (doubling): Theorem 1.1 (a fixed subset S of real ℓ₂ with doubling constant at most 76800 and no
  bi-Lipschitz embedding into ℝ^k for any k ≥ 1 at any finite distortion), with the source's definitions of
  "doubling with constant at most λ" and "bi-Lipschitz embedding with distortion at most D"; and, as a second
  theorem, the compact obstruction announced in the last paragraph for every infinite-dimensional real Banach
  space (universal doubling constant, no bi-Lipschitz embedding into any finite-dimensional real normed space).
- O28 (siegel): Theorem 1.1, with L(s, χ) the analytic continuation of the Dirichlet series (Mathlib has
  `DirichletCharacter.LFunction`; say how you know it is that continuation), for primitive nonprincipal real χ of
  conductor q ≥ 3.
In a comment block below each file's code: every ambiguity and your choice. Avoid junk values and say how.
Check each file compiles: `cd /home/claude/formalization && export PATH=$HOME/.elan/bin:$PATH && lake env lean <file>`
(`sorry` only in the reading theorems).
