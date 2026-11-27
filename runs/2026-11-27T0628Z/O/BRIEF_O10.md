# Blind reading brief: target O, family O10 "An explicit noncoordinate polynomial with affine three-space zero fibre" (OpenAI release)

Committed before any reader runs. Readers A (Opus), B (Sonnet), C (Haiku), each alone.
You have NOT seen, and must not look for, any Lean formalization of this claim. Read only this brief and
`noncoord/sources/paper_lines25-121.tex` (verbatim TeX, paper.tex sha256 prefix 60993c0b524291b7). Do not open
or list any other file or directory of the repository or under /home/claude/ext; no web. You may read
Mathlib's source (/home/claude/formalization/.lake/packages/mathlib) for names.

Write ONE Lean 4 file, `import Mathlib` only, at `noncoord/<your letter>/reading.lean`, with:
- the source's polynomial F ∈ ℂ[h,u,v,w] (as an `MvPolynomial (Fin 4) ℂ`), typed from (eq:xyz)–(eq:F);
- `theorem reading_thm_quotient`: R/(F) ≅ ℂ^[3] (ℂ-algebra isomorphism with a polynomial ring in 3 variables);
- `theorem reading_thm_gradient`: every partial derivative of F vanishes at (2, 0, −1/2, 1/2);
- `theorem reading_thm_noncoordinate`: F is not a coordinate of R (say how you define "coordinate");
- `theorem reading_cor`: Corollary 1.2 (every n ≥ 4), as literally as possible;
all `:= sorry`. In a comment block below: every ambiguity and your choice (variable order, what ℂ^[n−1] means,
ℕ subtraction in n − 1). Check it compiles:
`cd /home/claude/formalization && export PATH=$HOME/.elan/bin:$PATH && lake env lean <file>`.
