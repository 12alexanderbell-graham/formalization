# Brief: blind literal reading of the Falkner–Skan separation window (run 2026-11-11T0232Z, second brief: the first handed over the denominator of the template)

You are an independent reader. Do not read anything in /home/claude/formalization except this brief and the output path below; in particular never open `Checked/`, `Work/`, `_archive/`, `runs/` (other than this folder), `scripts/`, `validation/`, `.lake/` or any `*.md` there, and do not use git to look at history. No web access.

## The problem

Falkner–Skan boundary layer in the β-form: f''' + f f'' + β(1 − (f')²) = 0 for η ≥ 0, f(0) = 0, f'(0) = 0, f'(η) → 1 as η → ∞. Write p = f', q = f''. The **separation value** β* is the (negative) value of β at which the attached solution has zero wall shear, q(0) = 0 (Hartree's separation profile; the solution approaches p → 1 faster than any exponential).

Jobs:
1. Compute β* yourself to at least 13 significant digits by TWO independent numerical routes (e.g. (a) shoot from f(0) = p(0) = q(0) = 0 with an arbitrary-precision integrator (mpmath) and bisect on β by whether p first exceeds 1 or turns back while below 1; (b) a different integrator or a matching condition at large η to the decaying tail). Report both values and their agreement.
2. Round β* outward to ten decimal places: write the two neighbouring ten-decimal numbers that enclose β* strictly as fractions −L/D and −U/D, where D is the power of ten that gives ten decimal places and L, U are natural numbers (L = U + 1). If β* lies so close to a ten-decimal number that your two routes disagree about L or U, say so and stop.
3. The claim's statement also restricts the positivity of q to the open half-line of η beyond the wall: give its left end Z (a plain numeral).
4. Fill in the template below.

Scripts and scratch files go to a temporary directory outside the repository (e.g. /tmp/sep_reader). `pip install --break-system-packages mpmath` if needed.

## What to write

ONE Lean 4 file `runs/2026-11-11T0232Z/sep_reader2/SecondReadingFSSep.lean`, with exactly the template below, `L`, `U`, `D`, `Z` replaced by your numerals (plain decimal natural numbers, no underscores). Nothing else changes except the module doc's reader/method fields.

```lean
import Mathlib.Data.Real.Basic
/-! Blind literal reading of the Falkner–Skan separation window (reader: <you>; method: <your two routes and their values>). -/
namespace Checked.Trust.SecondReading
open Set
/-- Falkner–Skan separation: β lies strictly between the outward ten-decimal roundings of the separation value β*. -/
def fsSepWindow (β : ℝ) : Prop := β ∈ Ioo (-(L / D : ℝ)) (-(U / D))
/-- Falkner–Skan problem: the open half-line of η beyond the wall. -/
def fsSepOpenHalfLine : Set ℝ := Ioi (Z : ℝ)
end Checked.Trust.SecondReading
```

Compile the file with `export PATH=$HOME/.elan/bin:$PATH; cd /home/claude/formalization; timeout 300 lake env lean runs/2026-11-11T0232Z/sep_reader2/SecondReadingFSSep.lean`. Do not run `lake build`. Do not commit.

Report: your two values of β*, L, U, D, Z, and what you used.
