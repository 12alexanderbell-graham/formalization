# Blind literal reading brief (run 2026-11-18T1628Z): how many Bonnor–Ebert spheres have a given mass

Do NOT read anything in the repository except this brief (no `Checked/`, `Work/`, other `runs/` folders, other `*.md` files, git history). Write only to `runs/2026-11-18T1628Z/be_count_reader/`. Do not compile Lean. Derive every answer yourself from the description below; you may run your own Python (numpy/scipy/mpmath) in a temporary directory outside the repository to check your reading numerically. If a web tool fails, is blocked or times out, record the source as "not read"; never fetch the same content with curl, wget or code. arXiv: arxiv.org/pdf only, never ar5iv or e-print.

Physics: a self-gravitating isothermal gas sphere in hydrostatic equilibrium, truncated at dimensionless radius s (s = 0 is the centre) and confined by an external pressure equal to the gas pressure there (the Bonnor–Ebert sphere). Its dimensionless mass m(s) is zero at the centre and, as a function of the truncation radius, has infinitely many turning points (extrema). Number all extrema of m as one sequence ξ indexed by the natural numbers 0, 1, 2, …, in increasing order of radius, starting with the first maximum (the critical Bonnor–Ebert sphere) and then alternating: maximum, minimum, maximum, minimum, … . Facts you may use: m is strictly increasing on the closed segment from the centre to the first maximum, strictly decreasing from each maximum to the next minimum and strictly increasing from each minimum to the next maximum; the first maximum is the largest value of m over all radii; each minimum is the smallest value of m over all radii from the preceding maximum on, and each later maximum is the largest value over all radii from the preceding minimum on; every maximum value lies above, and every minimum value below, the mass of the singular isothermal sphere, which is also the limit of m at large radius. For a positive number μ let N(μ) be the number of radii s ≥ 0 with m(s) = μ (the number of equilibrium spheres of that mass, temperature and external pressure).

Fill in the capital placeholders A to K in this Lean template — keep every other character, including the import lines, the doc comments and the line breaks, exactly as written — and write it to `runs/2026-11-18T1628Z/be_count_reader/SecondReadingBECount.lean`:

```lean
import Mathlib.Data.Real.Basic
/-! Blind literal reading for the number of Bonnor–Ebert spheres of a given mass (run 2026-11-18T1628Z). -/
namespace Checked.Trust.SecondReading
/-- Bonnor–Ebert sphere: the radius of the first minimum of the mass, for the sequence ξ of extrema. -/
def beFirstMinRadius (ξ : ℕ → ℝ) : ℝ := ξ A
/-- Bonnor–Ebert sphere: the radius of the second maximum of the mass, for the sequence ξ of extrema. -/
def beSecondMaxRadius (ξ : ℕ → ℝ) : ℝ := ξ B
/-- Bonnor–Ebert sphere: the radius of the second minimum of the mass, for the sequence ξ of extrema. -/
def beSecondMinRadius (ξ : ℕ → ℝ) : ℝ := ξ C
/-- Bonnor–Ebert sphere: the radius of the third maximum of the mass, for the sequence ξ of extrema. -/
def beThirdMaxRadius (ξ : ℕ → ℝ) : ℝ := ξ D
/-- Bonnor–Ebert sphere: the index of the (k+2)-th minimum of the mass in the sequence of extrema. -/
def beNextMinIndex (k : ℕ) : ℕ := E
/-- Bonnor–Ebert sphere: the number of spheres of a mass strictly above the first maximum value. -/
def beCountAboveCritical : ℕ := F
/-- Bonnor–Ebert sphere: the number of spheres of a mass strictly between the value at the (k+2)-th maximum and the value at the (k+1)-th maximum. -/
def beCountFallBand (k : ℕ) : ℕ := G
/-- Bonnor–Ebert sphere: the number of spheres of a mass equal to the value at the (k+2)-th maximum. -/
def beCountAtMax (k : ℕ) : ℕ := H
/-- Bonnor–Ebert sphere: the number of spheres of a mass equal to the value at the (k+1)-th minimum. -/
def beCountAtMin (k : ℕ) : ℕ := I
/-- Bonnor–Ebert sphere: the number of spheres of a mass strictly between the value at the (k+1)-th minimum and the value at the (k+2)-th minimum. -/
def beCountRiseBand (k : ℕ) : ℕ := J
/-- Bonnor–Ebert sphere: the number of spheres of a positive mass strictly below the value at the first minimum. -/
def beCountBelowFirstMin : ℕ := K
end Checked.Trust.SecondReading
```

- A, B, C, D: natural-number literals (indices in the sequence ξ described above).
- E, G, H, I, J: for an arbitrary natural number k, write each as `a * k + b` with natural-number literals a and b (write `a * k` alone, no `+ b`, when b is zero).
- F, K: natural-number literals.

Also write `notes.md` in the same folder: your derivation of each count in a few lines (and, if you like, a numerical check), and anything you were unsure of. Report both files' contents in your final message.
