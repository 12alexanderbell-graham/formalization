# Brief: blind literal reading of twelve tabulated Falkner–Skan rows with decelerating outer stream, reversed-flow table (this run; second brief, paths given relative to this brief so that no date appears in it)

You are an independent reader. This brief is a file in a folder R/ under /home/claude/formalization (you were given its path). Do not read anything in /home/claude/formalization except this brief, the image named below and the output file below; in particular never open `Checked/`, `Work/`, `_archive/`, `scripts/`, `validation/`, `.lake/`, any other file under `runs/`, or any `*.md` other than this brief, and do not use git to look at history.

## The problem

Steady two-dimensional boundary layer of an incompressible fluid (kinematic viscosity ν) on a wall y = 0, x > 0, under an outer (inviscid) stream U(x) = a·x^m (a > 0, −1 < m): the Falkner–Skan family (flow past a wedge; for m < 0 the outer stream decelerates). Look for a similarity solution of the boundary-layer equations with

* similarity variable η = y·√((m + 1)·U(x) / (2 ν x)),
* stream function ψ = √(2 ν x U(x) / (m + 1)) · f(η), so u = ∂ψ/∂y and v = −∂ψ/∂x,

with no slip and no penetration at the wall and u → U(x) at the edge of the layer. The problem reduces to a third-order ODE for f on η ≥ 0 containing one pressure-gradient coefficient (Hartree's parameter β), which depends on m.

The rows wanted are printed in **B. D. Ganapol, arXiv:1006.3888 (version v1), Table 7 (the reversed-flow table), page 23**: a column of values of Hartree's parameter β and a column of wall shears α = f''(0). A crop of that table, rendered from the typeset PDF, is the image `ganapol_table7.png` in the folder `typeset/` next to the folder R/ (i.e. `R/../typeset/ganapol_table7.png`) (open it with the Read tool). You may also download `https://arxiv.org/pdf/1006.3888v1` with `curl -sSfL` into a temporary directory outside the repository, find the page with `pdftotext -f 23 -l 23`, render it with `pdftoppm -r 200 -png -f 23 -l 23` and look at the PNG, to confirm the crop. Also check the paper's own form of the equation against your derivation if the paper states it.

Your job:

1. **Derive the ODE in exactly this normalisation** (η and ψ as above; do not rescale) for general m and identify Hartree's parameter as the coefficient multiplying the pressure-gradient term. With p = f' and q = f'', write the ODE as q' = an expression in f, p, q. In the template below it must have the shape `-(f η * q η) - (BETA) * (A - p η ^ C)`. A and C are plain integer numerals. If your derived equation does not have this shape, say so in the module doc and in the report and do not force it.
2. Check your derivation symbolically (e.g. sympy: substitute ψ into the boundary-layer momentum equation with the outer-flow pressure gradient U U').
3. **Read β of twelve rows of Table 7.** Count the rows of the table body from the top: the first row below the column header is the first row. The rows wanted are the fourth, fifth, sixth, seventh, eighth, ninth, eleventh, twelfth, thirteenth, fourteenth, fifteenth and sixteenth (the tenth is not wanted). Each value is printed in E-notation. Write it as an ordinary decimal with the fewest decimal digits that represent it exactly, then as an exact fraction `-n / d` where d is 10 raised to that number of decimal digits (no reduction; minus sign directly in front of the numerator, no space).
4. **Fill in the template below**: `BETA_FOUR` is β of the fourth row, `BETA_FIVE` of the fifth row, and so on (`BETA_SIXTEEN` of the sixteenth row).

Scripts, the PDF, text dumps and renders go to a temporary directory outside the repository (e.g. /tmp/claude-0/fsrev_reader_b). Web rules: a failed, blocked or timed-out WebFetch/WebSearch is recorded as "not read" — never fetch the same content with curl, wget or code; for arXiv only arxiv.org/abs or arxiv.org/pdf, never ar5iv or e-print.

## What to write

ONE Lean 4 file `SecondReadingFSRevTable.lean` in the folder R/ (next to this brief), with exactly the template below. Replace each capital placeholder by your numeral: `A`, `C` plain integer numerals (the same in all twelve definitions); the twelve `BETA_…` as described in job 3. Nothing else changes: keep every other token, the parentheses and the order exactly as shown.

```lean
import Mathlib.Data.Real.Basic
/-! Blind literal reading of twelve tabulated Falkner–Skan wedge rows with decelerating outer stream, reversed-flow table (reader: <you>; derivation and checks: <what you used>). -/
namespace Checked.Trust.SecondReading
/-- Falkner–Skan wedge flow at the fourth row of the reversed-flow table: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsRevRowFourRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (BETA_FOUR) * (A - p η ^ C)
/-- Falkner–Skan wedge flow at the fifth row of the reversed-flow table: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsRevRowFiveRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (BETA_FIVE) * (A - p η ^ C)
/-- Falkner–Skan wedge flow at the sixth row of the reversed-flow table: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsRevRowSixRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (BETA_SIX) * (A - p η ^ C)
/-- Falkner–Skan wedge flow at the seventh row of the reversed-flow table: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsRevRowSevenRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (BETA_SEVEN) * (A - p η ^ C)
/-- Falkner–Skan wedge flow at the eighth row of the reversed-flow table: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsRevRowEightRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (BETA_EIGHT) * (A - p η ^ C)
/-- Falkner–Skan wedge flow at the ninth row of the reversed-flow table: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsRevRowNineRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (BETA_NINE) * (A - p η ^ C)
/-- Falkner–Skan wedge flow at the eleventh row of the reversed-flow table: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsRevRowElevenRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (BETA_ELEVEN) * (A - p η ^ C)
/-- Falkner–Skan wedge flow at the twelfth row of the reversed-flow table: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsRevRowTwelveRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (BETA_TWELVE) * (A - p η ^ C)
/-- Falkner–Skan wedge flow at the thirteenth row of the reversed-flow table: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsRevRowThirteenRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (BETA_THIRTEEN) * (A - p η ^ C)
/-- Falkner–Skan wedge flow at the fourteenth row of the reversed-flow table: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsRevRowFourteenRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (BETA_FOURTEEN) * (A - p η ^ C)
/-- Falkner–Skan wedge flow at the fifteenth row of the reversed-flow table: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsRevRowFifteenRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (BETA_FIFTEEN) * (A - p η ^ C)
/-- Falkner–Skan wedge flow at the sixteenth row of the reversed-flow table: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsRevRowSixteenRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (BETA_SIXTEEN) * (A - p η ^ C)
end Checked.Trust.SecondReading
```

No other definitions and no comments other than the module doc and the docstrings above (fill in the module doc's reader/method).

Compile the file with `export PATH=$HOME/.elan/bin:$PATH; cd /home/claude/formalization; timeout 300 lake env lean <path of your file relative to /home/claude/formalization>`. Do not run `lake build`. Do not commit.

Finally report: your general-m equation, Hartree's parameter as a function of m, the twelve β values as printed and as you converted them, A, C; the twelve printed wall shears of those rows; whether the paper's equation agrees with yours; your symbolic check; anything uncertain.
