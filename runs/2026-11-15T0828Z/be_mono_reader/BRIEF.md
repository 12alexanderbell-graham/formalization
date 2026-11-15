# Blind literal reading brief (run 2026-11-15T0828Z): the segments of the Bonnor–Ebert mass–radius curve between its turning points

Do NOT read anything in the repository except this brief (no `Checked/`, `Work/`, other `runs/` folders, other `*.md` files, git history). Write only to `runs/2026-11-15T0828Z/be_mono_reader/`. Do not compile Lean. Derive every number yourself from the description below; you may run your own Python (numpy/scipy/mpmath) in a temporary directory outside the repository to check your reading numerically. If a web tool fails, is blocked or times out, record the source as "not read"; never fetch the same content with curl, wget or code. arXiv: arxiv.org/pdf only, never ar5iv or e-print.

Physics: a self-gravitating isothermal gas sphere in hydrostatic equilibrium, truncated at dimensionless radius ξ (ξ = 0 is the centre) and confined by an external pressure equal to the gas pressure there (the Bonnor–Ebert sphere). Its dimensionless mass m, as a function of the truncation radius, has infinitely many turning points (extrema). The claim being checked numbers all extrema of m as one sequence ξ indexed by the natural numbers 0, 1, 2, …, in increasing order of radius, starting with the first maximum (the critical Bonnor–Ebert sphere), and then alternating: maximum, minimum, maximum, minimum, … . It states that m is strictly increasing on the closed segment from the centre to the first maximum, strictly decreasing on each closed segment from a maximum to the next minimum, and strictly increasing on each closed segment from a minimum to the next maximum.

Fill in the capital placeholders A, B, C, D, E, F in this Lean template — keep every other character, including the import lines, the doc comments and the line breaks, exactly as written — and write it to `runs/2026-11-15T0828Z/be_mono_reader/SecondReadingBEMono.lean`:

```lean
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Data.Real.Basic
/-! Blind literal reading for the monotone segments of the Bonnor–Ebert mass (run 2026-11-15T0828Z). -/
namespace Checked.Trust.SecondReading
open Set
/-- Bonnor–Ebert sphere: the closed segment of radii from the centre to the first maximum of the mass, for the sequence ξ of extrema. -/
def beRiseFromCentre (ξ : ℕ → ℝ) : Set ℝ := Icc A (ξ B)
/-- Bonnor–Ebert sphere: the closed segment of radii from the (k+1)-th maximum of the mass to the next minimum, for the sequence ξ of extrema. -/
def beFallSegment (ξ : ℕ → ℝ) (k : ℕ) : Set ℝ := Icc (ξ (C)) (ξ (D))
/-- Bonnor–Ebert sphere: the closed segment of radii from the (k+1)-th minimum of the mass to the next maximum, for the sequence ξ of extrema. -/
def beRiseSegment (ξ : ℕ → ℝ) (k : ℕ) : Set ℝ := Icc (ξ (E)) (ξ (F))
end Checked.Trust.SecondReading
```

- A: the dimensionless radius of the centre. B: the index, in the sequence described above, of the first maximum.
- C, D: for an arbitrary natural number k, the indices of the (k+1)-th maximum and of the minimum that follows it. E, F: the indices of the (k+1)-th minimum and of the maximum that follows it. Write each as `a * k + b` with natural-number literals a and b, and write `a * k` alone (no `+ b`) when b is zero.

Also write `notes.md` in the same folder: your derivation in a few lines (and, if you like, a numerical check of the first few extrema of m), and anything you were unsure of. Report both files' contents in your final message.
