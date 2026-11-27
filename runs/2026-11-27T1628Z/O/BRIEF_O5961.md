# Blind reading brief: target O, families O59 "Generalized star height at most three", O60 "Ordinary two-point correlations of multiplicative functions", O61 "A cubic lower bound for border determinantal complexity of the permanent" (OpenAI release)

Committed before any reader runs. Readers A (Opus), B (Sonnet), C (Haiku), each alone, all three families.
You have NOT seen, and must not look for, any Lean formalization of these claims. Read exactly these files and
no others: this brief; `starheight/sources/abstract_and_introduction_lines1-41.tex` (abstract + introduction.tex
lines 1-41, sha256 prefix e7bfe4b04fbc90c0); `elliott/sources/abstract_and_introduction_lines1-99.tex` (abstract +
introduction.tex lines 1-99, 077b0a2f551aeb8e); `permanent/sources/abstract_and_introduction_lines1-65.tex`
(abstract + introduction.tex lines 1-65, af7a79e73bb0e3f6). All paths are under
/home/claude/formalization/runs/2026-11-27T1628Z/O/. Do not list directories (no `ls`), do not use wildcards or
globs in any path, do not open anything else in the repository or under /tmp or /home/claude/ext; no web. You may
read Mathlib's source (/home/claude/formalization/.lake/packages/mathlib) for names. Macros: \sht is the
(generalized) star height, \eps the empty word; \C, \N the complexes and naturals; \per the permanent, \dc and
\bdc the determinantal and border determinantal complexity, \Mat_n(\C) the n×n complex matrices; \Cref and \cite
are references.

Write each file at exactly /home/claude/formalization/runs/2026-11-27T1628Z/O/<family>/<your letter>/reading.lean,
where <family> is one of the three words `starheight`, `elliott`, `permanent` (create the directory with
`mkdir -p` of that exact path). One Lean 4 file per family, `import Mathlib` only, wrapped in
`namespace Reader<your letter>`, with every definition written by you from the source (Mathlib's language,
automata, arithmetic-function, Dirichlet-character, polynomial, matrix and topology notions may be used), and the
claims as `theorem reading… : … := sorry`, as literally as possible:
- O59 (starheight): Theorem 1.1 (every regular language over every finite alphabet has generalized star height
  at most three; the expressions and their height as the text defines them; "regular" in a standard sense, say
  which).
- O60 (elliott): Theorem 1.1 (the absolute c > 0 and the Liouville bound for every admissible affine pair),
  Theorem 1.2 (binary corrected Elliott, the distance and uniform nonpretentiousness as the text defines them),
  and Corollary 1.3 (affine correlations).
- O61 (permanent): Theorem 1.1 (bdc(per_m) ≥ c m³ for m ≥ m₀, with the stated c = 1/(5 529 600 e) and
  m₀ = 1408; bdc as the text defines it) and the next paragraph's claim that the same numerical bound holds for
  exact determinantal complexity.
In a comment block below each file's code: every ambiguity and your choice. Avoid junk values (ℕ subtraction,
x/0 = 0, sSup/sInf/iSup/iInf of empty or unbounded sets, ⊤ in ℕ∞- or ℝ≥0∞-valued quantities, `Nat.find`/least
elements that may not exist, `Real.log` of non-positive numbers, `Real.sqrt` of negatives) and say how.
Check each file compiles: `cd /home/claude/formalization && export PATH=$HOME/.elan/bin:$PATH && lake env lean <file>`
(`sorry` only in the reading theorems; allow a few minutes per compile). If a notion has no usable Mathlib
counterpart, define it yourself from the text, or state in the comment block exactly which part you could not
write and why. Reply with the three paths and a one-line summary each; do not commit.
