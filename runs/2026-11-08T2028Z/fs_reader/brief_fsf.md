# Brief: blind literal reading of one Falkner–Skan problem (run 2026-11-08T2028Z)

You are an independent reader. Do not read anything in /home/claude/formalization except this brief and the output path below; in particular never open `Checked/`, `Work/`, `_archive/`, `runs/` (other than this folder), `scripts/`, `validation/`, `.lake/` or any `*.md` there, and do not use git to look at history.

## The problem

Steady two-dimensional boundary layer of an incompressible fluid (kinematic viscosity ν) on a wall y = 0, x > 0, under an outer (inviscid) stream U(x) = a·x^m (a > 0). This is the Falkner–Skan family (flow past a wedge). Look for a similarity solution of the boundary-layer equations with

* similarity variable η = y·√((m + 1)·U(x) / (2 ν x)),
* stream function ψ = √(2 ν x U(x) / (m + 1)) · f(η), so u = ∂ψ/∂y and v = −∂ψ/∂x,

with no slip and no penetration at the wall and u → U(x) at the edge of the layer. The problem reduces to a third-order ODE for f on η ≥ 0. The case wanted is the wedge with **m = 1/9**.

You have three jobs.

1. **Derive the ODE and the boundary conditions in exactly this normalisation** (η and ψ as defined above; do not rescale), for general m and then for m = 1/9. With p = f' and q = f'', write the ODE as q' = an expression in f, p, q. In the template below it must have the shape `-(f η * q η) - BETA * (A - p η ^ C)`: BETA is the coefficient that depends on m, evaluated at m = 1/9 and written as an exact fraction `n / d` (two integer numerals with ` / ` between them; if it is an integer write it as an integer); A and C are plain integer numerals. If your derived equation does not have this shape, say so in the module doc and in the report and do not force it. Give the value Z of η at the wall (a plain integer numeral).

2. **Compute σ = f''(wall) for m = 1/9 yourself.** Do not look it up; compute it, e.g. by shooting with high precision (Python `mpmath`, at least 30 significant digits): f = f' = 0 at the wall, f'' = s there, and solve for s such that f' tends to its edge value. Check it by a second, independent route (a second precision and a second method or integration length). Estimate your error. Then let `L` be σ − 10⁻¹⁰ and `U` be σ + 10⁻¹⁰, **each rounded to the nearest number with exactly ten digits after the decimal point**; write both with all ten digits after the point (keep trailing zeros). If your error estimate does not decide a rounding, say so.

3. **Fill in the template below.**

Scripts and scratch files go to a temporary directory outside the repository (e.g. /tmp/fsf_reader). Web access is not needed; if you use it: a failed, blocked or timed-out WebFetch/WebSearch is recorded as "not read" — never fetch the same content with curl, wget or code; for arXiv only arxiv.org/abs or arxiv.org/pdf, never ar5iv or e-print. Do not take σ from any web page or book: the point is an independent computation.

## What to write

ONE Lean 4 file `runs/2026-11-08T2028Z/fs_reader/SecondReadingFSFifth.lean`, with exactly the template below. Replace each capital placeholder by your numeral: `A`, `C`, `Z` plain integer numerals from job 1 (`Z` stands in two places, the same numeral); `BETA` your exact fraction; `L`, `U` your ten-decimal numbers written as plain decimals (digits, one point, the digits after it). Nothing else changes: keep every other token, the parentheses and the order exactly as shown.

```lean
import Mathlib.Data.Real.Basic
/-! Blind literal reading of a Falkner–Skan wedge problem (reader: <you>; derivation, computation and sources: <what you used>). -/
namespace Checked.Trust.SecondReading
/-- Falkner–Skan wedge flow with m = 1/9: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsfWedgeRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - BETA * (A - p η ^ C)
/-- Falkner–Skan wedge flow with m = 1/9: the wall value of q = f'' lies strictly between σ − 10⁻¹⁰ and σ + 10⁻¹⁰, each rounded to ten decimals. -/
def fsfWedgeShear (q : ℝ → ℝ) : Prop := L < q Z ∧ q Z < U
end Checked.Trust.SecondReading
```

No other definitions and no comments other than the module doc and the docstrings above (fill in the module doc's reader/sources/method).

Compile the file with `export PATH=$HOME/.elan/bin:$PATH; cd /home/claude/formalization; timeout 300 lake env lean runs/2026-11-08T2028Z/fs_reader/SecondReadingFSFifth.lean`. Do not run `lake build`. Another build is running on the machine; that is expected, do not stop it. Do not commit.

Finally report: your general-m equation, BETA, A, C, Z; σ with all digits you trust, your error estimate and how you got it (two methods or precisions); L, U; what you consulted; anything uncertain.
