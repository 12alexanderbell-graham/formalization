# Brief: blind literal reading of one tabulated Falkner–Skan row with decelerating outer stream, reversed-flow table (copy of an earlier brief, one row, named by its printed wall shear)

You are an independent reader. This brief is a file in a folder R/ under /home/claude/formalization (you were given its path). Do not read anything in /home/claude/formalization except this brief, the image named below and the output file below; in particular never open `Checked/`, `Work/`, `_archive/`, `scripts/`, `validation/`, `.lake/`, any other file under `runs/`, or any `*.md` other than this brief, and do not use git to look at history.

## The problem

Steady two-dimensional boundary layer of an incompressible fluid (kinematic viscosity ν) on a wall y = 0, x > 0, under an outer (inviscid) stream U(x) = a·x^m (a > 0, −1 < m): the Falkner–Skan family (flow past a wedge; for m < 0 the outer stream decelerates). Look for a similarity solution of the boundary-layer equations with

* similarity variable η = y·√((m + 1)·U(x) / (2 ν x)),
* stream function ψ = √(2 ν x U(x) / (m + 1)) · f(η), so u = ∂ψ/∂y and v = −∂ψ/∂x,

with no slip and no penetration at the wall and u → U(x) at the edge of the layer. The problem reduces to a third-order ODE for f on η ≥ 0 containing one pressure-gradient coefficient (Hartree's parameter β), which depends on m.

The row wanted is printed in **B. D. Ganapol, arXiv:1006.3888 (version v1), Table 7 (the reversed-flow table), page 23**: a column of values of Hartree's parameter β and a column of wall shears α = f''(0). A crop of that table, rendered from the typeset PDF, is the image `ganapol_table7.png` in the folder `typeset/` next to the folder R/ (i.e. `R/../../2026-11-13T0228Z/typeset/ganapol_table7.png`) (open it with the Read tool). You may also download `https://arxiv.org/pdf/1006.3888v1` with `curl -sSfL` into a temporary directory outside the repository, find the page with `pdftotext -f 23 -l 23`, render it with `pdftoppm -r 200 -png -f 23 -l 23` and look at the PNG, to confirm the crop. Also check the paper's own form of the equation against your derivation if the paper states it.

Your job:

1. **Derive the ODE in exactly this normalisation** (η and ψ as above; do not rescale) for general m and identify Hartree's parameter as the coefficient multiplying the pressure-gradient term. With p = f' and q = f'', write the ODE as q' = an expression in f, p, q. In the template below it must have the shape `-(f η * q η) - (BETA) * (A - p η ^ C)`. A and C are plain integer numerals. If your derived equation does not have this shape, say so in the module doc and in the report and do not force it.
2. Check your derivation symbolically (e.g. sympy: substitute ψ into the boundary-layer momentum equation with the outer-flow pressure gradient U U').
3. **Read β of the one wanted row.** The wanted row is the single row of the table body whose printed wall shear α, in E-notation, begins with the digits 6.51 after its minus sign (look at the whole column: exactly one row qualifies; if none or more than one does, stop and say so). Its β is printed in E-notation. Write it as an ordinary decimal with the fewest decimal digits that represent it exactly, then as an exact fraction `-n / d` where d is 10 raised to that number of decimal digits (no reduction; minus sign directly in front of the numerator, no space).
4. **Fill in the template below**: the placeholder `BETA_A` gets that row's β.

Scripts, the PDF, text dumps and renders go to a temporary directory outside the repository (e.g. /tmp/claude-0/fsrev_reader_w). Web rules: a failed, blocked or timed-out WebFetch/WebSearch is recorded as "not read" — never fetch the same content with curl, wget or code; for arXiv only arxiv.org/abs or arxiv.org/pdf, never ar5iv or e-print.

## What to write

ONE Lean 4 file `SecondReadingFSRevRowTwo.lean` in the folder R/ (next to this brief), with exactly the template below. Replace each capital placeholder by your numeral: `A`, `C` plain integer numerals (the same in every definition); the `BETA_…` as described in jobs 3 and 4. Nothing else changes: keep every other token, the parentheses and the order exactly as shown.

```lean
import Mathlib.Data.Real.Basic
/-! Blind literal reading of one tabulated Falkner–Skan wedge row with decelerating outer stream, reversed-flow table (reader: <you>; derivation and checks: <what you used>). -/
namespace Checked.Trust.SecondReading
/-- Falkner–Skan wedge flow at one row of the reversed-flow table (the row this definition's placeholder names in the brief): the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsRevRowTwoRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (BETA_A) * (A - p η ^ C)
end Checked.Trust.SecondReading
```

No other definitions and no comments other than the module doc and the docstrings above (fill in the module doc's reader/method).

Compile the file with `export PATH=$HOME/.elan/bin:$PATH; cd /home/claude/formalization; timeout 300 lake env lean <path of your file relative to /home/claude/formalization>`. Do not run `lake build`. Do not commit.

Finally report: your general-m equation, Hartree's parameter as a function of m, the wanted β as printed and as you converted it, A, C; the printed wall shear of that row; whether the paper's equation agrees with yours; your symbolic check; anything uncertain.
