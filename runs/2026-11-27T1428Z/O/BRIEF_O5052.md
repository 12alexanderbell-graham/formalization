# Blind reading brief: target O, families O50 "The Gaussian propeller conjecture in every dimension", O51 "A factor-two approximation for shortest common superstring", O52 "A torsion-free hyperbolic group that is neither residually finite nor linear" (OpenAI release)

Committed before any reader runs. Readers A (Opus), B (Sonnet), C (Haiku), each alone, all three families.
You have NOT seen, and must not look for, any Lean formalization of these claims. Read exactly these files and
no others: this brief; `propeller/sources/abstract_and_introduction_lines36-117.tex` (main.tex lines 36-117,
sha256 prefix d1aa9486b7ba5823); `superstring/sources/abstract_and_introduction_lines1-12.tex` (abstract +
01-introduction.tex lines 1-12, e44180a9745515a2); `hyperbolic/sources/abstract_and_introduction_lines48-74.tex`
(paper.tex lines 48-74, 49e6e78edc6fb178). All paths are under /home/claude/formalization/runs/2026-11-27T1428Z/O/.
Do not list directories (no `ls`), do not use wildcards or globs in any path, do not open anything else in the
repository or under /tmp; no web. You may read Mathlib's source (/home/claude/formalization/.lake/packages/mathlib)
for names. Macros: \OPT is the optimum length; \len{T} is the length of T.

Write each file at exactly /home/claude/formalization/runs/2026-11-27T1428Z/O/<family>/<your letter>/reading.lean,
where <family> is one of the three words `propeller`, `superstring`, `hyperbolic` (create the directory with
`mkdir -p` of that exact path). One Lean 4 file per family, `import Mathlib` only, wrapped in
`namespace Reader<your letter>`, with every definition written by you from the source (Mathlib's measure,
Gaussian, integral, list, computability, group and graph notions may be used), and the claims as
`theorem reading… : … := sorry`, as literally as possible:
- O50 (propeller): Theorem 1.1, both its inequality and its sharpness sentence (two theorems, or one conjunction).
- O51 (superstring): Theorem 1.1 (a deterministic algorithm, polynomial in the total encoded input size, that
  outputs a common superstring of length at most 2·OPT). Say in the comment block how you model "algorithm",
  "polynomial in the encoded input size" and the encoding of symbols and strings.
- O52 (hyperbolic): Theorem 1.1 (a torsion-free word-hyperbolic group that is not residually finite), and, as a
  second theorem, the corollary's last sentence (that group is not linear over any commutative field) stated for
  the same group as Theorem 1.1 (conjoined).
In a comment block below each file's code: every ambiguity and your choice. Avoid junk values (ℕ subtraction,
x/0 = 0, integrals of non-integrable functions = 0, sSup/sInf of empty or unbounded sets, ⊤ in ℕ∞-valued
quantities) and say how.
Check each file compiles: `cd /home/claude/formalization && export PATH=$HOME/.elan/bin:$PATH && lake env lean <file>`
(`sorry` only in the reading theorems). Reply with the three paths and a one-line summary each; do not commit.
