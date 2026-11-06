# Brief: blind literal reading of the Robertson (1966) rate constants (run 2026-11-06T0428Z)

You are an independent reader. Do not read anything in /home/claude/formalization except this brief and the output path below; in particular never open `Checked/`, `Work/`, `runs/` (other than this folder), `scripts/`, or any `*.md` there. Find the published values yourself (web search; prefer the primary paper — H. H. Robertson, "The solution of a set of reaction rate equations", 1966 — or a standard textbook/test-set description of "Robertson's chemical kinetics problem"; record which source you used and whether you saw the typeset text or a secondary transcription). For arXiv use only arxiv.org/abs or arxiv.org/pdf pages (never ar5iv, never e-print).

Write ONE Lean 4 file `runs/2026-11-06T0428Z/rob_reader/SecondReadingRob.lean`:

```lean
import Mathlib.Data.Real.Basic
/-! Blind literal reading of Robertson's rate constants (reader: <you>, sources: <list>). -/
namespace Checked.Trust.SecondReading
/-- Robertson (1966): rate constant of the reaction A → B. -/
noncomputable def robK1 : ℝ := ...
/-- Robertson (1966): rate constant of the reaction B + C → A + C. -/
noncomputable def robK2 : ℝ := ...
/-- Robertson (1966): rate constant of the reaction 2B → B + C. -/
noncomputable def robK3 : ℝ := ...
/-- Robertson (1966): initial concentrations of A, B, C (in this order), as a triple. -/
noncomputable def robInit : ℝ × ℝ × ℝ := ...
/-- The end time of the standard integration interval [0, T] of the original problem. -/
noncomputable def robT : ℝ := ...
end Checked.Trust.SecondReading
```

Form of each body: an exact rational written with integer literals and `/`, `*`, `^` only (for example a printed 0.5 becomes `1 / 2`, a printed 2·10^5 becomes `2 * 10 ^ 5`), exactly the value printed in the source. No other definitions, no comments other than the module doc and docstrings above. Use only what you read; if two sources disagree, say so in the module doc and use the primary one. Compile the file with `export PATH=$HOME/.elan/bin:$PATH; cd /home/claude/formalization; lake env lean runs/2026-11-06T0428Z/rob_reader/SecondReadingRob.lean` (timeout 300000 ms).

Finally report: the five bodies, the sources, and anything uncertain.
