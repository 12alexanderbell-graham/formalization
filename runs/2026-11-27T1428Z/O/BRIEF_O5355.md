# Blind reading brief: target O, families O53 "Rigidity of the Turing degrees", O54 "The Kadison–Ringrose cohomology conjecture", O55 "Strong Kadison–Kastler stability" (OpenAI release)

Committed before any reader runs. Readers A (Opus), B (Sonnet), C (Haiku), each alone, all three families.
You have NOT seen, and must not look for, any Lean formalization of these claims. Read exactly these files and
no others: this brief; `turing/sources/abstract_and_introduction_lines1-32.tex` (abstract + introduction.tex lines
1-32, sha256 prefix ede74f9f9ad1a031); `hochschild/sources/abstract_and_introduction_lines1-56.tex` (abstract +
01-introduction.tex lines 1-56, 2ef11044095e8a7a); `kadisonkastler/sources/abstract_and_introduction_lines1-31.tex`
(abstract + 01-introduction.tex lines 1-31, 62a407eca5e15b06). All paths are under
/home/claude/formalization/runs/2026-11-27T1428Z/O/. Do not list directories (no `ls`), do not use wildcards or
globs in any path, do not open anything else in the repository or under /tmp; no web. You may read Mathlib's
source (/home/claude/formalization/.lake/packages/mathlib) for names. Macros: \DT is the set of Turing degrees,
\leT is Turing reducibility, \norm{x} the norm, \B(H) the bounded operators on H, \eps is ε.

Write each file at exactly /home/claude/formalization/runs/2026-11-27T1428Z/O/<family>/<your letter>/reading.lean,
where <family> is one of the three words `turing`, `hochschild`, `kadisonkastler` (create the directory with
`mkdir -p` of that exact path). One Lean 4 file per family, `import Mathlib` only, wrapped in
`namespace Reader<your letter>`, with every definition written by you from the source (Mathlib's computability,
order, operator-algebra, Hilbert-space and multilinear-map notions may be used), and the claims as
`theorem reading… : … := sorry`, as literally as possible:
- O53 (turing): Theorem 1.1 (every order automorphism of the Turing degrees is the identity).
- O54 (hochschild): Theorem 1.1 (complex von Neumann algebra M, k ≥ 2, every bounded k-cochain f with df = 0 is dg
  for a bounded (k−1)-cochain g; the differential as the text defines it).
- O55 (kadisonkastler): Theorem 1.1 (the uniform δ(ε), every complex Hilbert space, unital von Neumann algebras at
  Kadison–Kastler distance < δ are conjugate by a unitary within ε of the identity; the distance as the text
  defines it).
In a comment block below each file's code: every ambiguity and your choice. Avoid junk values (ℕ subtraction,
x/0 = 0, sSup/sInf/iSup of empty or unbounded sets, ⊤ in ℕ∞- or
ℝ≥0∞-valued quantities) and say how.
Check each file compiles: `cd /home/claude/formalization && export PATH=$HOME/.elan/bin:$PATH && lake env lean <file>`
(`sorry` only in the reading theorems; allow a few minutes per compile). Reply with the three paths and a one-line
summary each; do not commit.
