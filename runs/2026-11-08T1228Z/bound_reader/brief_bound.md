# Brief: blind literal reading of two velocity-profile conditions (run 2026-11-08T1228Z)

You are an independent reader. Do not read anything in /home/claude/formalization except this brief and the output path below; in particular never open `Checked/`, `Work/`, `_archive/`, `runs/` (other than this folder), `scripts/`, `validation/`, `.lake/` or any `*.md` there, and do not use git to look at history.

## The setting

Steady stagnation-point boundary layers (plane Hiemenz flow and axisymmetric Homann flow) against a wall. Far from the wall the outer inviscid flow has streamwise velocity U(x) = a x (a > 0). The similarity solution writes the streamwise velocity inside the layer as u(x, η) = a x · f'(η), where η ≥ 0 is the similarity coordinate normal to the wall (η = 0 at the wall). In the code below `p` stands for f' as a function of η, so `p η` is the ratio u / U at height η.

## Your job

Translate each of the following two conditions on the velocity profile, at a height η, into a condition on `p η`:

1. **Bounded by the outer speed:** the streamwise velocity u at height η is, in absolute value, at most the outer speed U (it may point backwards, but never faster than U in either direction; equality allowed).
2. **Forward and below the outer speed:** the streamwise velocity u at height η points forward or vanishes (it is not negative) and is strictly smaller than the outer speed U.

Write each as two inequalities joined by `∧`, in the shapes `A ≤ p η ∧ p η ≤ B` and `C ≤ p η ∧ p η < D`, where `A`, `B`, `C`, `D` are numerals (integers; a negative value is written with a leading minus sign directly before the digit, e.g. `-7`). Work out the numerals yourself from the description above.

## What to write

ONE Lean 4 file `runs/2026-11-08T1228Z/bound_reader/SecondReadingBound.lean`, with exactly the template below. Replace each capital placeholder by your numeral. Nothing else changes: keep every other token, the parentheses and the order exactly as shown.

```lean
import Mathlib.Data.Real.Basic
/-! Blind literal reading of two velocity-profile conditions for stagnation-point boundary layers (reader: <you>; reasoning: <one sentence>). -/
namespace Checked.Trust.SecondReading
/-- Stagnation-point boundary layers: at height η the streamwise velocity is, in absolute value, at most the outer speed (p η is the ratio u / U). -/
def stagSpeedBounded (p : ℝ → ℝ) (η : ℝ) : Prop := A ≤ p η ∧ p η ≤ B
/-- Stagnation-point boundary layers: at height η the streamwise velocity is not negative and strictly below the outer speed (p η is the ratio u / U). -/
def stagForwardBelow (p : ℝ → ℝ) (η : ℝ) : Prop := C ≤ p η ∧ p η < D
end Checked.Trust.SecondReading
```

No other definitions and no comments other than the module doc and the docstrings above (fill in the module doc's reader/reasoning). Compile the file with `export PATH=$HOME/.elan/bin:$PATH; cd /home/claude/formalization; lake env lean runs/2026-11-08T1228Z/bound_reader/SecondReadingBound.lean` (timeout 600000 ms; the machine is busy, it may take a few minutes). Do not run `lake build`. No web access is needed; do not use it.

Finally report A, B, C, D and one sentence of reasoning for each.
