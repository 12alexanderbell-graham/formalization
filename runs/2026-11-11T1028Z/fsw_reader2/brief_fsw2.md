# Brief: blind literal reading of a tabulated Falkner–Skan row with adverse pressure gradient (run 2026-11-11T1028Z, second brief: the first, in `fsw_reader/`, printed the value to be read and was withdrawn unused)

You are an independent reader. Do not read anything in /home/claude/formalization except this brief and the output path below; in particular never open `Checked/`, `Work/`, `_archive/`, `runs/` (other than this folder), `scripts/`, `validation/`, `.lake/` or any `*.md` there, and do not use git to look at history.

## The problem

Steady two-dimensional boundary layer of an incompressible fluid (kinematic viscosity ν) on a wall y = 0, x > 0, under an outer (inviscid) stream U(x) = a·x^m (a > 0, −1 < m): the Falkner–Skan family (flow past a wedge; for m < 0 the outer stream decelerates). Look for a similarity solution of the boundary-layer equations with

* similarity variable η = y·√((m + 1)·U(x) / (2 ν x)),
* stream function ψ = √(2 ν x U(x) / (m + 1)) · f(η), so u = ∂ψ/∂y and v = −∂ψ/∂x,

with no slip and no penetration at the wall and u → U(x) at the edge of the layer. The problem reduces to a third-order ODE for f on η ≥ 0 containing one pressure-gradient coefficient (Hartree's parameter), which depends on m. The row wanted is the one printed in **R. Fazio, arXiv:1212.5057 (version v1), page 16**: the text there reports, for the value of Hartree's parameter used in that paragraph (a decelerating case close to separation), two wall-shear values f''(0) of opposite sign. Read Hartree's parameter of that paragraph from the typeset page: download `https://arxiv.org/pdf/1212.5057v1` with `curl -sSfL` into a temporary directory outside the repository, find the page with `pdftotext -f 16 -l 16`, render it with `pdftoppm -r 200 -png -f 16 -l 16` and look at the PNG (Read tool). Also check the paper's own form of the equation (its eq. (1.5)) against your derivation.

Your job:

1. **Derive the ODE in exactly this normalisation** (η and ψ as above; do not rescale) for general m, identify Hartree's parameter as the coefficient multiplying the pressure-gradient term, and give m for the row described above. With p = f' and q = f'', write the ODE as q' = an expression in f, p, q. In the template below it must have the shape `-(f η * q η) - (BETA) * (A - p η ^ C)`: BETA is Hartree's parameter of that paragraph, written as the printed decimal turned into an exact fraction `-n / d` where d is 10 raised to the number of printed decimal digits (no reduction; minus sign directly in front of the numerator, no space). A and C are plain integer numerals. If your derived equation does not have this shape, say so in the module doc and in the report and do not force it.
2. Check your derivation symbolically (e.g. sympy: substitute ψ into the boundary-layer momentum equation with the outer-flow pressure gradient U U').
3. **Fill in the template below.**

Scripts, the PDF, text dumps and renders go to a temporary directory outside the repository (e.g. /tmp/claude-0/fsw_reader2). Web rules: a failed, blocked or timed-out WebFetch/WebSearch is recorded as "not read" — never fetch the same content with curl, wget or code; for arXiv only arxiv.org/abs or arxiv.org/pdf, never ar5iv or e-print.

## What to write

ONE Lean 4 file `runs/2026-11-11T1028Z/fsw_reader2/SecondReadingFSNearSep.lean`, with exactly the template below. Replace each capital placeholder by your numeral: `A`, `C` plain integer numerals; `BETA` as described in job 1. Nothing else changes: keep every other token, the parentheses and the order exactly as shown.

```lean
import Mathlib.Data.Real.Basic
/-! Blind literal reading of a tabulated Falkner–Skan wedge row with decelerating outer stream (reader: <you>; derivation and checks: <what you used>). -/
namespace Checked.Trust.SecondReading
/-- Falkner–Skan wedge flow at the tabulated decelerating row near separation: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsNearSepWedgeRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (BETA) * (A - p η ^ C)
end Checked.Trust.SecondReading
```

No other definitions and no comments other than the module doc and the docstring above (fill in the module doc's reader/method).

Compile the file with `export PATH=$HOME/.elan/bin:$PATH; cd /home/claude/formalization; timeout 300 lake env lean runs/2026-11-11T1028Z/fsw_reader2/SecondReadingFSNearSep.lean`. Do not run `lake build`. Do not commit.

Finally report: your general-m equation, Hartree's parameter as a function of m, m for this row, BETA, A, C; the two printed wall-shear values of that paragraph as you read them; whether the paper's equation agrees with yours; your symbolic check; anything uncertain.
