# Brief: blind literal reading of the Falkner–Skan equation with a general pressure-gradient parameter (run 2026-11-09T0428Z)

You are an independent reader. Do not read anything in /home/claude/formalization except this brief and the output path below; in particular never open `Checked/`, `Work/`, `_archive/`, `runs/` (other than this folder), `scripts/`, `validation/`, `.lake/` or any `*.md` there, and do not use git to look at history.

## The problem

Steady two-dimensional boundary layer of an incompressible fluid (kinematic viscosity ν) on a wall y = 0, x > 0, under an outer (inviscid) stream U(x) = a·x^m (a > 0, m > −1). This is the Falkner–Skan family (flow past a wedge). Look for a similarity solution of the boundary-layer equations with

* similarity variable η = y·√((m + 1)·U(x) / (2 ν x)),
* stream function ψ = √(2 ν x U(x) / (m + 1)) · f(η), so u = ∂ψ/∂y and v = −∂ψ/∂x,

with no slip and no penetration at the wall and u → U(x) at the edge of the layer. The problem reduces to a third-order ODE for f on η ≥ 0 with one parameter depending on m.

You have three jobs.

1. **Derive the ODE in exactly this normalisation** (η and ψ as defined above; do not rescale) for general m. With p = f' and q = f'', write it as q' = an expression in f, p, q. In the template below it must have the shape `-(f η * q η) - β * (A - p η ^ C)`, where β is the one coefficient that depends on m. Give β as a formula in m, and A and C as plain integer numerals. If your derived equation does not have this shape (for example if the coefficient of f q is not 1 in this normalisation), say so in the module doc and in the report and do not force it.

2. **Range.** Say for which values of m the parameter β lies in the half-open interval 0 < β ≤ 1, and which physical flows the two ends of that range are (state the m and the flow at each end).

3. **Check your equation** independently: substitute your ODE back into the boundary-layer momentum equation u ∂u/∂x + v ∂u/∂y = U dU/dx + ν ∂²u/∂y² symbolically (e.g. sympy), for general m, and report that the residual vanishes identically. Also check one special case you know by a second route (e.g. m = 0, or the plane stagnation point m = 1).

Scripts and scratch files go to a temporary directory outside the repository (e.g. /tmp/fsb_reader). Web access is not needed; if you use it: a failed, blocked or timed-out WebFetch/WebSearch is recorded as "not read" — never fetch the same content with curl, wget or code; for arXiv only arxiv.org/abs or arxiv.org/pdf, never ar5iv or e-print.

## What to write

ONE Lean 4 file `runs/2026-11-09T0428Z/fsb_reader/SecondReadingFSBeta.lean`, with exactly the template below. Replace `A`, `C` by your plain integer numerals and `<FORMULA>` in the docstring by your formula for β in terms of m (plain text). Nothing else in the code line changes: keep every other token, the parentheses and the order exactly as shown.

```lean
import Mathlib.Data.Real.Basic
/-! Blind literal reading of the Falkner–Skan equation with a general parameter (reader: <you>; derivation, check and sources: <what you used>). -/
namespace Checked.Trust.SecondReading
/-- Falkner–Skan wedge flow with outer stream a·x^m and parameter β = <FORMULA>: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsBetaRhs (β : ℝ) (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - β * (A - p η ^ C)
end Checked.Trust.SecondReading
```

No other definitions and no comments other than the module doc and the docstring above (fill in the module doc's reader/sources/method).

Compile the file with `export PATH=$HOME/.elan/bin:$PATH; cd /home/claude/formalization; timeout 300 lake env lean runs/2026-11-09T0428Z/fsb_reader/SecondReadingFSBeta.lean`. If `lake` is not yet available (Lean is being installed on the machine), wait a few minutes and retry; if after 20 minutes it still is not available, write the file anyway and say so. Do not run `lake build`. Another build may be running on the machine; that is expected, do not stop it. Do not commit.

Finally report: your general-m equation, the formula for β, A, C; the m-range for 0 < β ≤ 1 and the flows at its ends; the symbolic check and the special case; what you consulted; anything uncertain.
