# Blind reading brief: target O, families O14 "An exponential bound for sunflowers", O15 "Asymptotically minimal maxima of real Littlewood polynomials", O16 "The dyadic case of the Erdős similarity conjecture" (OpenAI release)

Committed before any reader runs. Readers A (Opus), B (Sonnet), C (Haiku), each alone, all three families.
You have NOT seen, and must not look for, any Lean formalization of these claims. Read exactly these files and
no others: this brief; `sunflower/sources/intro_lines1-30.tex` (intro.tex sha256 prefix c28b44293f448e41);
`littlewood/sources/introduction_lines1-36.tex` (7efbdbff0d7905b6); `dyadic/sources/introduction_lines1-34.tex`
(c26e982dedb26a7a). Do not list directories, do not use wildcards or globs in any path, do not open anything
else in the repository or under /home/claude/ext; no web. You may read Mathlib's source
(/home/claude/formalization/.lake/packages/mathlib) for names.

For each family write ONE Lean 4 file, `import Mathlib` only, at `<family>/<your letter>/reading.lean`, with
every definition written by you from the source, and the headline theorem(s) as `theorem reading… : … := sorry`,
as literally as possible:
- O14 (sunflower): Theorem 1.1 — both its qualitative form (a constant B_r) and its quantitative form with the
  stated B_r = 2^{C H⁴ L^{5/2}}, H = log₂(2r), L = log₂(2H), C absolute.
- O15 (littlewood): Theorem 1.1 — the "lim m_N = 1" form with the source's m_N, and the "Equivalently" form.
- O16 (dyadic): Theorem 1.1 — both forms (x + sD ⊄ E_η, and the "Equivalently" form), D as the source defines it.
In a comment block below each file's code: every ambiguity and your choice. Avoid junk values and say how.
Check each file compiles: `cd /home/claude/formalization && export PATH=$HOME/.elan/bin:$PATH && lake env lean <file>`.
