# Blind reading: common instructions (external test, target S)

You are given ONLY the source text of a mathematical claim (an Erdős problem as stated on
erdosproblems.com, and the headline theorem of a manuscript claiming to resolve it). You have not
seen, and must not look for, any existing Lean formalization of it.

Task: write ONE self-contained Lean 4 file (Mathlib, `import Mathlib` only) containing
- every definition the statement needs, written by you from the source text, with a doc comment
  quoting the source sentence it encodes;
- `theorem reading : <the manuscript's headline theorem, as literally as possible> := by sorry`;
- `theorem reading_erdos : <the Erdős problem's question, answered affirmatively> := by sorry`
  if it differs from `reading` (otherwise omit it and say so).
Avoid junk values: no ℕ subtraction where a negative could arise, no `sInf` of a possibly empty
set without stating nonemptiness, no division by a possibly zero term. Use ℝ for logarithms
and real powers.

Then, below the code in a comment block, list every place where the source text was ambiguous
and which reading you chose and why.

Do not open any file outside the directory you are told to write in. Do not search the web.
