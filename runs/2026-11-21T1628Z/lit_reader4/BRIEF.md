# Blind literal reading brief (run 2026-11-21T1628Z): the residual condition of a cubic Hubble-diagram comparison

Do NOT read anything in the repository except this brief (no `Checked/`, `Work/`, other `runs/` folders, other `*.md` files, git history). Write only to `runs/2026-11-21T1628Z/lit_reader4/`. Do not compile Lean.

Cosmology: a cubic log-polynomial fit of the Hubble diagram is compared with an exact flat ΛCDM universe at three sources. At each source the claim requires that the distance modulus of the ratio `d` of the exact luminosity distance to the fitted one (five times the base-ten logarithm of `d`, in magnitudes) differs from one common offset `c` by at most five hundredths of a magnitude in absolute value.

Fill in the capital placeholders K, L, I, J in this Lean template with natural-number literals (the smallest that express the quantity in the form given; for the window, a fraction in lowest terms) — keep every other character, including the import line, the doc comments and the line breaks, exactly as written — and write it to `runs/2026-11-21T1628Z/lit_reader4/SecondReadingB1A3Residual.lean`:

```lean
import Mathlib.Analysis.SpecialFunctions.Log.Base
/-! Blind literal reading of the residual condition of the three-source cubic fit (run 2026-11-21T1628Z). -/
namespace Checked.Trust.SecondReading
/-- Three-source cubic fit: the distance modulus of the ratio `d` is within the window of the common offset `c`. -/
def b1a3Residual (d c : ℝ) : Prop := |K * Real.logb L d - c| ≤ I / J
end Checked.Trust.SecondReading
```

Also write `notes.md` in the same folder: your reasoning in a few lines. Report both files' contents in your final message.
