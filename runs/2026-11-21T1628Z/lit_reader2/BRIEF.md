# Blind literal reading brief (run 2026-11-21T1628Z): the three sources, the window and the expansion law of a cubic Hubble-diagram fit

Do NOT read anything in the repository except this brief (no `Checked/`, `Work/`, other `runs/` folders, other `*.md` files, git history). Write only to `runs/2026-11-21T1628Z/lit_reader2/`. Do not compile Lean. arXiv: arxiv.org/pdf only, never ar5iv or e-print (you should not need any source).

Cosmology: a cubic log-polynomial fit of the Hubble diagram is compared with an exact spatially flat ΛCDM universe of matter density Ω. The claim being checked places three sources at one plus redshift equal to the square root of two, twice the square root of two, and four times the square root of two; it compares distance moduli (five times the base-ten logarithm of a distance ratio, in magnitudes) within a window of five hundredths of a magnitude; and in the universe the squared Hubble rate over its present value is the flat ΛCDM expression in Ω and the redshift z (matter scaling as the cube of one plus z, and the cosmological constant making up the rest so that the expression is one today).

Fill in the capital placeholders A … O in this Lean template with natural-number literals — keep every other character, including the import line, the doc comments and the line breaks, exactly as written — and write it to `runs/2026-11-21T1628Z/lit_reader2/SecondReadingB1A3.lean`:

```lean
import Mathlib.Analysis.SpecialFunctions.Log.Base
/-! Blind literal reading of the three-source cubic fit (run 2026-11-21T1628Z). -/
namespace Checked.Trust.SecondReading
/-- Three-source cubic fit: the redshift of the nearest source. -/
noncomputable def b1a3zNear : ℝ := √A - B
/-- Three-source cubic fit: the redshift of the middle source. -/
noncomputable def b1a3zMid : ℝ := C * √D - E
/-- Three-source cubic fit: the redshift of the farthest source. -/
noncomputable def b1a3zFar : ℝ := F * √G - H
/-- Three-source cubic fit: the window on the distance moduli, in magnitudes, as a fraction. -/
noncomputable def b1a3Window : ℝ := I / J
/-- Three-source cubic fit: the distance modulus of a distance ratio `x`, up to the common offset. -/
noncomputable def b1a3Modulus (x : ℝ) : ℝ := K * Real.logb L x
/-- Three-source cubic fit: the squared Hubble rate over its present value in flat ΛCDM, at redshift `z`. -/
noncomputable def b1a3Radicand (Ω z : ℝ) : ℝ := Ω * (M + z) ^ N + O - Ω
end Checked.Trust.SecondReading
```

Use the smallest natural numbers that express each quantity in the form given (for the window, a fraction in lowest terms).

Also write `notes.md` in the same folder: your reasoning in a few lines and anything you were unsure of. Report both files' contents in your final message.
