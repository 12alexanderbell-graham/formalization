# Blind reading brief: target O, families O62 "Kadison's similarity theorem through uniform derivation estimates", O63 "The strong thin tree conjecture", O64 "Brennan's conjecture and sharp inverse-square integral means" (OpenAI release)

Committed before any reader runs. Readers A (Opus), B (Sonnet), C (Haiku), each alone, all three families.
You have NOT seen, and must not look for, any Lean formalization of these claims. Read exactly these files and
no others: this brief; `kadison/sources/abstract_and_introduction_lines1-32_95-134.tex` (abstract + introduction.tex
lines 1-32 and 95-134, sha256 prefix 1e47e8af9117ae83); `thintree/sources/abstract_and_introduction_lines1-27.tex`
(abstract + introduction.tex lines 1-27, b82189b5a052e4eb); `brennan/sources/abstract_and_introduction_lines1-91.tex`
(abstract + 00-introduction.tex lines 1-91, f32837b0e6648552). All paths are under
/home/claude/formalization/runs/2026-11-27T1628Z/O/. Do not list directories (no `ls`), do not use wildcards or
globs in any path, do not open anything else in the repository or under /tmp or /home/claude/ext; no web. You may
read Mathlib's source (/home/claude/formalization/.lake/packages/mathlib) for names: search it with the Grep tool
(a Bash `grep` may be refused). Macros: \C, \CC, \R the complexes and reals; \B, \mathcal B(H) the bounded
operators; \DD the open unit disk; \SSS the schlicht class; \dd A area measure; \dist the distance; \Cref, \cite,
\citep are references.

Write each file at exactly /home/claude/formalization/runs/2026-11-27T1628Z/O/<family>/<your letter>/reading.lean,
where <family> is one of the three words `kadison`, `thintree`, `brennan` (create the directory with `mkdir -p` of
that exact path). One Lean 4 file per family, `import Mathlib` only, wrapped in `namespace Reader<your letter>`,
with every definition written by you from the source (Mathlib's C⋆-algebra, von Neumann algebra, operator,
graph, complex-analysis, integration and filter notions may be used), and the claims as
`theorem reading… : … := sorry`, as literally as possible:
- O62 (kadison): Theorem 1.1 (similarity), Theorem 1.2 (uniform commutator estimate, g_P and the amplifications as
  the text defines them) and Corollary 1.3 (universal hyperreflexivity, α_M as the text defines it, with the same C).
- O63 (thintree): Theorem 1.1 (the universal C, multigraphs, cuts, k-edge-connectivity and spanning trees as the
  text defines them).
- O64 (brennan): Theorem 1.1 (all four assertions: the uniform bound, B_S(−2) = 1, the domain form, the disk form;
  M_t, β_f and B_S as the text defines them) and Corollary 1.2 (the Koebe function).
In a comment block below each file's code: every ambiguity and your choice. Avoid junk values (ℕ subtraction,
x/0 = 0, sSup/sInf/iSup/iInf of empty or unbounded sets, `Real.log` of non-positive numbers, `Real.rpow` of
negative bases, `deriv` of non-differentiable functions, integrals of non-integrable functions (`∫` is 0 then),
⊤/⊥ in extended quantities) and say how.
Check each file compiles: `cd /home/claude/formalization && export PATH=$HOME/.elan/bin:$PATH && lake env lean <file>`
(`sorry` only in the reading theorems; allow a few minutes per compile). If a notion has no usable Mathlib
counterpart, define it yourself from the text, or state in the comment block exactly which part you could not
write and why. Reply with the three paths and a one-line summary each; do not commit.
