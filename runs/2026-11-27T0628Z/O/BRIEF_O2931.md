# Blind reading brief: target O, families O29 "The sharp logarithmic exponent of r(5,t)", O30 "The subcritical Hénon–Lane–Emden conjecture", O31 "Relative independence of the separable quotient problem" (OpenAI release)

Committed before any reader runs. Readers A (Opus), B (Sonnet), C (Haiku), each alone, all three families.
You have NOT seen, and must not look for, any Lean formalization of these claims. Read exactly these files and
no others: this brief; `ramsey5/sources/introduction_lines1-29.tex` (introduction.tex sha256 prefix
d7ffbe8e1545c4a6); `henon/sources/introduction_lines1-68.tex` (01-introduction.tex, 6f100de228636b2e);
`sepquot/sources/introduction_lines1-56.tex` (introduction.tex, 743da2df4441eedf). All paths are under
/home/claude/formalization/runs/2026-11-27T0628Z/O/. Do not list directories, do not use wildcards or globs in any
path, do not open anything else in the repository or under /home/claude/ext; no web. You may read Mathlib's source
(/home/claude/formalization/.lake/packages/mathlib) for names.

For each family write ONE Lean 4 file, `import Mathlib` only, at
/home/claude/formalization/runs/2026-11-27T0628Z/O/<family>/<your letter>/reading.lean, wrapped in
`namespace Reader<your letter>`, with every definition written by you from the source, and the claims as
`theorem reading… : … := sorry`, as literally as possible:
- O29 (ramsey5): Theorem 1.1 — the two-sided bound (one theorem) and the limit (a second theorem), with the
  source's r(s, t).
- O30 (henon): Theorem 1.1 and Corollary 1.2, each its own theorem; Δ the Laplacian on ℝⁿ (Mathlib has
  `InnerProductSpace.laplacian` / `Laplacian.laplacian`; say which you use and why), C²(ℝⁿ∖{0}) ∩ C(ℝⁿ) as you judge
  most literal.
- O31 (sepquot): SQ_𝔽 for 𝔽 ∈ {ℝ, ℂ} as defined in the excerpt; Theorem 1.1 (i) and (ii) as theorems
  (for (i), define "real-valued measurable" as the excerpt does; for (ii), CH as you judge most literal); state
  in a comment, not as a theorem, why the consistency/independence conclusions and Corollary 1.2 can or cannot be
  stated in Lean, and state them if you can.
In a comment block below each file's code: every ambiguity and your choice. Avoid junk values (`sInf` of an empty
set, `log` of small arguments, `rpow` of negatives, …) and say how.
Check each file compiles: `cd /home/claude/formalization && export PATH=$HOME/.elan/bin:$PATH && lake env lean <file>`
(`sorry` only in the reading theorems).
