# Blind reading brief: target O, O64b "A strict inverse-first-power bound for univalent functions" (second paper of family O64), O65 "Sharp projection-body inequalities and a counterexample to simplex maximization", O66 "Exponential state costs for two-way automata" (OpenAI release)

Committed before any reader runs. Readers A (Opus), B (Sonnet), C (Haiku), each alone, all three families.
You have NOT seen, and must not look for, any Lean formalization of these claims. Read exactly these files and
no others: this brief; `strict/sources/abstract_and_introduction_lines1-56.tex` (abstract + 00-introduction.tex
lines 1-56, sha256 prefix c92bd3a77ed81a33); `projection/sources/two_papers_excerpts.tex` (two papers: abstract +
introduction of each, as marked inside, 62ac23b772963ab0); `automata/sources/two_papers_excerpts.tex` (two papers:
abstract + introduction parts of each, as marked inside, 840db66bcf3e86bf). All paths are under
/home/claude/formalization/runs/2026-11-27T1828Z/O/. Do not list directories (no `ls`), do not use wildcards or
globs in any path, do not open anything else in the repository or under /tmp or /home/claude/ext; no web. You may
read Mathlib's source (/home/claude/formalization/.lake/packages/mathlib) for names: search it with the Grep tool
(a Bash `grep` may be refused). Macros: \C, \R (in the strict and projection files) the complexes and reals; \DD
the open unit disk; \SSS the normalized schlicht class; \HH the upper half-plane; \conv convex hull; \vol, \proj,
\ip as written; in the automata file's second paper \R{H} is the monoid $\mathcal R_H$ of all binary relations on
$H$, \Id{F} the identity relation on $F$, \OWL the language name OWL, \eps the empty word, \NFA 2NFA, \DFA 2DFA;
\Cref, \cite, \citep, \eqref are references.

Write each file at exactly /home/claude/formalization/runs/2026-11-27T1828Z/O/<family>/<your letter>/reading.lean,
where <family> is one of the three words `strict`, `projection`, `automata` (create the directory with `mkdir -p`
of that exact path). One Lean 4 file per family, `import Mathlib` only, wrapped in `namespace Reader<your letter>`,
with every definition written by you from the source (Mathlib's complex-analysis, integration, filter, convex
geometry, measure, finite-type and relation notions may be used), and the claims as
`theorem reading… : … := sorry`, as literally as possible:
- O64b (strict): Theorem 1.1 (the uniform bound with its constants, the consequence `B_b(-1) < 1/4`, and the
  statement that Kraetzer's conjectured identity is false; M_p, β_f, S, S_b and B_b as the text defines them).
- O65 (projection): paper 1 Theorem 1.1 (the inequality for every n ≥ 4 and every convex body, and the equality
  case); paper 2 Theorem 1.1 (the exact value of R_20(K)/c_20 for K = T_10 × T_10 and that it exceeds 1) and its
  Corollary (exponential excess). Projection body, support function, R_d and c_d as the text defines them.
- O66 (automata): paper 1 Theorem 1.1 (the n-state 2NFA for L_H and the lower bound for its complement) and its
  Corollary (determinization); paper 2 Theorem 1.1 (both sentences, and the s + 1 variant) and its Corollary
  (no polynomial simulation). Two-way automata, acceptance, state counts and the languages as the text defines
  them (write the automaton model yourself from the text).
In a comment block below each file's code: every ambiguity and your choice. Avoid junk values (ℕ subtraction,
x/0 = 0, sSup/sInf/iSup/iInf of empty or unbounded sets, `Real.log` of non-positive numbers, `Real.rpow` of
negative bases, `deriv` of non-differentiable functions, integrals of non-integrable functions (`∫` is 0 then),
⊤/⊥ in extended quantities) and say how. Write no decimals or fractions in a `/-! -/` module doc.
Check each file compiles: `cd /home/claude/formalization && export PATH=$HOME/.elan/bin:$PATH && lake env lean <file>`
(`sorry` only in the reading theorems; allow a few minutes per compile). If a notion has no usable Mathlib
counterpart, define it yourself from the text, or state in the comment block exactly which part you could not
write and why. Reply with the three paths and a one-line summary each; do not commit.
