# Blind reading brief: target O, families O17 "Almost-everywhere Fourier convergence in L log L", O18 "A power saving for planar unit distances", O19 "A universal group of type F∞" (OpenAI release)

Committed before any reader runs. Readers A (Opus), B (Sonnet), C (Haiku), each alone, all three families.
You have NOT seen, and must not look for, any Lean formalization of these claims. Read exactly these files and
no others: this brief; `llogl/sources/introduction_lines1-27.tex` (01-introduction.tex sha256 prefix
61ad5332e7a5cd16); `unitdist/sources/introduction_lines1-20.tex` (00-introduction.tex, 25a795fb4910068b);
`finfty/sources/introduction_lines1-23.tex` (introduction.tex, 069ab99e406f6ae8). All paths are under
/home/claude/formalization/runs/2026-11-27T0628Z/O/. Do not list directories, do not use wildcards or globs in any
path, do not open anything else in the repository or under /home/claude/ext; no web. You may read Mathlib's source
(/home/claude/formalization/.lake/packages/mathlib) for names.

For each family write ONE Lean 4 file, `import Mathlib` only, at
/home/claude/formalization/runs/2026-11-27T0628Z/O/<family>/<your letter>/reading.lean, with every definition
written by you from the source, and the headline claim(s) as `theorem reading… : … := sorry`, as literally as
possible:
- O17 (llogl): Theorem 1.1 — every complex f in L log L(𝕋) has symmetric Fourier partial sums S_N f converging
  to f almost everywhere. Use the source's normalisation of 𝕋, μ, f̂ and S_N.
- O18 (unitdist): Theorem 1.1 — u(n) ≤ C n^β with absolute 0 < C and 1 ≤ β < 4/3, for every n; and the
  "equivalently" form u(n) = O(n^{4/3 − δ}) for an absolute δ > 0. u(X) counts unordered pairs of distinct points
  at Euclidean distance 1; u(n) is the maximum over n-point sets.
- O19 (finfty): Theorem 1.1 — a group H of type F∞ into which every finitely presented group embeds; and
  Corollary 1.2 (a finitely generated group embeds in H iff it is recursively presented). Define type F∞ from the
  source's own words (a connected CW complex with finitely many cells in each dimension, fundamental group H,
  contractible universal cover). If Mathlib lacks an object you need (e.g. recursive presentability), define it
  yourself as literally as you can, or say precisely why you could not.
In a comment block below each file's code: every ambiguity and your choice. Avoid junk values and say how.
Check each file compiles: `cd /home/claude/formalization && export PATH=$HOME/.elan/bin:$PATH && lake env lean <file>`
(`sorry` only in the reading theorems).
