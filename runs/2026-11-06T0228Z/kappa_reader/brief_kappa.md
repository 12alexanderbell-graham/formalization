# Brief: blind literal reading of three published κ(ω) correlations (run 2026-11-06T0228Z)

You are an independent reader. Do not read anything in /home/claude/formalization or /home/claude/fz2 except this brief and the output path below; in particular never open `Checked/`, `Work/`, `runs/` (other than this folder), `scripts/`, or any `*.md` there. Find the published values yourself (web search; prefer the primary paper or a textbook/handbook table; record which source you used and whether you saw the typeset text or a secondary transcription).

Write ONE Lean 4 file `runs/2026-11-06T0228Z/kappa_reader/SecondReadingKappa.lean`:

```lean
import Mathlib.Data.Real.Basic
/-! Blind literal reading of three κ(ω) correlations (reader: <you>, sources: <list>). -/
namespace Checked.Trust.SecondReading
/-- Peng and Robinson (1976): κ as a function of the acentric factor ω. -/
noncomputable def kappaPR76 (ω : ℝ) : ℝ := ...
/-- Robinson and Peng (1978) revision, branch for heavier components (ω above about 0.49). -/
noncomputable def kappaPR78 (ω : ℝ) : ℝ := ...
/-- Soave (1972) for the Soave–Redlich–Kwong equation: the coefficient m (also written κ) as a function of ω. -/
noncomputable def kappaSoave (ω : ℝ) : ℝ := ...
end Checked.Trust.SecondReading
```

Form of each body: a polynomial in ω written as terms in increasing powers, `c0 + c1 * ω - c2 * ω ^ 2 ...`, each coefficient a decimal exactly as printed in the source (all printed digits, including trailing zeros), the operator `+` or `-` carrying the printed sign of the term (never `+ -c`), the constant term without `* ω ^ 0`, the linear term as `c1 * ω` (no `^ 1`). No other definitions, no comments other than the module doc and docstrings above, no program names. Use only what you read; if two sources disagree, say so in the module doc and use the primary one.

Finally report: the three bodies, the sources, and anything uncertain.
