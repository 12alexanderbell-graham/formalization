# Blind reading brief: target O, families O56 "Positive lower density of large prime gaps", O57 "Squarefree values of quartics and power-free values of polynomials", O58 "An algebra of infinite little finitistic dimension" (OpenAI release)

Committed before any reader runs. Readers A (Opus), B (Sonnet), C (Haiku), each alone, all three families.
You have NOT seen, and must not look for, any Lean formalization of these claims. Read exactly these files and
no others: this brief; `primegaps/sources/abstract_and_introduction_lines1-53.tex` (abstract + 01-introduction.tex
lines 1-53, sha256 prefix e4f2a7716d5bfde9); `powerfree/sources/abstract_and_introduction_lines1-42_110-120.tex`
(abstract + 01-introduction.tex lines 1-42 and 110-120, 72ada3e5824262aa);
`finitistic/sources/abstract_and_introduction_lines1-112.tex` (abstract + 01-introduction.tex lines 1-112,
1cfa513d81996589). All paths are under /home/claude/formalization/runs/2026-11-27T1628Z/O/. Do not list
directories (no `ls`), do not use wildcards or globs in any path, do not open anything else in the repository or
under /tmp or /home/claude/ext; no web. You may read Mathlib's source (/home/claude/formalization/.lake/packages/mathlib)
for names. Macros: \Z, \Q, \R, \C are the integers, rationals, reals, complexes; \pd is projective dimension,
\findim the little and \Findim the big finitistic dimension; \Cref and \cite are references.

Write each file at exactly /home/claude/formalization/runs/2026-11-27T1628Z/O/<family>/<your letter>/reading.lean,
where <family> is one of the three words `primegaps`, `powerfree`, `finitistic` (create the directory with
`mkdir -p` of that exact path). One Lean 4 file per family, `import Mathlib` only, wrapped in
`namespace Reader<your letter>`, with every definition written by you from the source (Mathlib's number-theory,
polynomial, asymptotics, module, category-theory and homological notions may be used), and the claims as
`theorem reading… : … := sorry`, as literally as possible:
- O56 (primegaps): Theorem 1.1 (for every fixed real C > 0, constants c(C) > 0 and N₀(C) with the count bound for
  every N ≥ N₀) and Corollary 1.2 (the set of n ≥ 1 with p_n/n < p_{n+1}/(n+1) has positive lower asymptotic
  density, the density as the text defines it).
- O57 (powerfree): Theorem 1.1 (degrees 4 ≤ d ≤ 8, k = d − 2) and Corollary 1.2 (every degree d ≥ 4), each with
  the asymptotic S_{f,k}(X) = c_{f,k} X + o_f(X) and c_{f,k} > 0, the Euler product and the counts as the text
  defines them.
- O58 (finitistic): Theorem 1.1 (the algebra A, the modules N_m, and "in particular fin.dim A = ∞") and
  Corollary 1.2 (Λ with the four finitistic dimensions, and the two injective-generation sentences).
In a comment block below each file's code: every ambiguity and your choice. Avoid junk values (ℕ subtraction,
x/0 = 0, sSup/sInf/iSup of empty or unbounded sets, ⊤ and ⊥ in ℕ∞-, WithBot ℕ∞- or ℝ≥0∞-valued quantities,
`Nat.nth` and `tprod`/`tsum` of non-summable or non-multipliable families) and say how.
Check each file compiles: `cd /home/claude/formalization && export PATH=$HOME/.elan/bin:$PATH && lake env lean <file>`
(`sorry` only in the reading theorems; allow a few minutes per compile). If a notion has no usable Mathlib
counterpart, define it yourself from the text, or state in the comment block exactly which part you could not
write and why. Reply with the three paths and a one-line summary each; do not commit.
