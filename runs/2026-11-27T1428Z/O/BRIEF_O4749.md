# Blind reading brief: target O, families O47 "Logarithmic and Lp Brunn–Minkowski inequalities", O48 "Tingley's sphere-isometry problem", O49 "A superquadratic separation of sensitivity and block sensitivity" (OpenAI release)

Committed before any reader runs. Readers A (Opus), B (Sonnet), C (Haiku), each alone, all three families.
You have NOT seen, and must not look for, any Lean formalization of these claims. Read exactly these files and
no others: this brief; `logbm/sources/abstract_and_introduction_lines1-83.tex` (abstract + introduction.tex lines
1-83, sha256 prefix 3c782e8b10a65586); `tingley/sources/abstract_and_introduction_lines43-59.tex` (main.tex lines
43-59, ea7c092b03cf839e); `sensitivity/sources/abstract_and_introduction_lines1-64.tex` (abstract +
00-introduction.tex lines 1-64, 58b6c6d16960cc1b). All paths are under
/home/claude/formalization/runs/2026-11-27T1428Z/O/. Do not list directories (no `ls`), do not use wildcards or
globs in any path, do not open anything else in the repository or under /tmp; no web. You may read Mathlib's
source (/home/claude/formalization/.lake/packages/mathlib) for names. Macros: \R is the reals, \E expectation,
\norm{x} is the norm of x, \abs{x} absolute value, \bs is block sensitivity.

For each family write ONE Lean 4 file, `import Mathlib` only, at
/home/claude/formalization/runs/2026-11-27T1428Z/O/<family>/<your letter>/reading.lean (create the directory with
`mkdir -p` of that exact path), wrapped in `namespace Reader<your letter>`, with every definition written by you
from the source (Mathlib's measure, convexity, normed-space, isometry and Boolean-function notions may be used),
and the claims as `theorem reading… : … := sorry`, as literally as possible:
- O47 (logbm): Theorem 1.1 (the even logarithmic Brunn–Minkowski inequality, with the support function and the
  Wulff body as the text defines them) and, as a second theorem, Corollary 1.2 (the symmetric L_p inequality).
- O48 (tingley): Theorem 1.1 in full (nonzero real Banach spaces, a surjective isometry of unit spheres; the map
  T is a surjective real-linear isometry, and it is the unique linear extension of f).
- O49 (sensitivity): Theorem 1.1 both as its first sentence (for every real C > 0 …) and its "More precisely"
  sentence (two theorems), and, as a third theorem, the abstract's last sentence ("for some fixed α > 2, our
  examples have unbounded block sensitivity and satisfy bs(f) ≥ s(f)^α"), as literally as you can (say in the
  comment block what "our examples" and "unbounded" quantify over in your reading).
In a comment block below each file's code: every ambiguity and your choice. Avoid junk values (ℕ subtraction,
x/0 = 0, real powers of nonpositive numbers, sSup/sInf of empty or unbounded sets, volumes equal to ⊤, ⊤ in
ℕ∞- or ℝ≥0∞-valued quantities) and say how.
Check each file compiles: `cd /home/claude/formalization && export PATH=$HOME/.elan/bin:$PATH && lake env lean <file>`
(`sorry` only in the reading theorems). Reply with the three paths and a one-line summary each; do not commit.
