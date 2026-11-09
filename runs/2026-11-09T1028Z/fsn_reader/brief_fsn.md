# Brief: blind literal reading of a Falkner–Skan problem with adverse pressure gradient (run 2026-11-09T1028Z)

You are an independent reader. Do not read anything in /home/claude/formalization except this brief and the output path below; in particular never open `Checked/`, `Work/`, `_archive/`, `runs/` (other than this folder), `scripts/`, `validation/`, `.lake/` or any `*.md` there, and do not use git to look at history.

## The problem

Steady two-dimensional boundary layer of an incompressible fluid (kinematic viscosity ν) on a wall y = 0, x > 0, under an outer (inviscid) stream U(x) = a·x^m (a > 0, −1 < m). This is the Falkner–Skan family (flow past a wedge; for m < 0 the outer stream decelerates). Look for a similarity solution of the boundary-layer equations with

* similarity variable η = y·√((m + 1)·U(x) / (2 ν x)),
* stream function ψ = √(2 ν x U(x) / (m + 1)) · f(η), so u = ∂ψ/∂y and v = −∂ψ/∂x,

with no slip and no penetration at the wall and u → U(x) at the edge of the layer. The problem reduces to a third-order ODE for f on η ≥ 0. The case wanted is the decelerating wedge flow with **m = −1/21**.

You have three jobs.

1. **Derive the ODE in exactly this normalisation** (η and ψ as defined above; do not rescale), for general m and then for m = −1/21. With p = f' and q = f'', write the ODE as q' = an expression in f, p, q. In the template below it must have the shape `-(f η * q η) - (BETA) * (A - p η ^ C)`: BETA is the coefficient that depends on m, evaluated at m = −1/21 and written as an exact reduced fraction `n / d` of two integer numerals with ` / ` between them and d > 0; if the value is negative, write the minus sign directly in front of the numerator (`-n / d`, no space after the minus); if it is an integer write it as an integer. A and C are plain integer numerals. If your derived equation does not have this shape, say so in the module doc and in the report and do not force it.

2. **Behaviour at the edge of the layer.** Let D be the value that p = f' tends to as η → ∞ in this normalisation (a plain integer numeral). For this m, solutions of the boundary-value problem with 0 ≤ f' ≤ D and f'' > 0 are known not to be unique. Linearise the ODE about the edge state (f ≈ η + const, p ≈ D) and find how the velocity defect D − p can decay as η → ∞: give the two kinds of decay (leading behaviour in η), and for each say how the ratio q / (D − p) behaves as η → ∞. Then say which kind of solution satisfies the condition "for every real number M, for all sufficiently large η, M · (D − p(η)) ≤ q(η)", and which kind does not. Check your linearisation symbolically (e.g. sympy), and if you can, check numerically on one solution of each kind (e.g. by shooting with scipy or mpmath).

3. **Fill in the template below.**

Scripts and scratch files go to a temporary directory outside the repository (e.g. /tmp/fsn_reader). Web access is not needed; if you use it: a failed, blocked or timed-out WebFetch/WebSearch is recorded as "not read" — never fetch the same content with curl, wget or code; for arXiv only arxiv.org/abs or arxiv.org/pdf, never ar5iv or e-print.

## What to write

ONE Lean 4 file `runs/2026-11-09T1028Z/fsn_reader/SecondReadingFSNeg.lean`, with exactly the template below. Replace each capital placeholder by your numeral: `A`, `C`, `D` plain integer numerals; `BETA` your exact fraction as described in job 1. Nothing else changes: keep every other token, the parentheses and the order exactly as shown.

```lean
import Mathlib.Data.Real.Basic
/-! Blind literal reading of a Falkner–Skan wedge problem with decelerating outer stream (reader: <you>; derivation, checks and sources: <what you used>). -/
namespace Checked.Trust.SecondReading
/-- Falkner–Skan wedge flow with m = −1/21: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsnWedgeRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (BETA) * (A - p η ^ C)
/-- Falkner–Skan problem: at height η, q = f'' is at least M times the velocity defect, the edge value of p = f' minus p η. -/
def fsnDefectBelow (M : ℝ) (p q : ℝ → ℝ) (η : ℝ) : Prop := M * (D - p η) ≤ q η
end Checked.Trust.SecondReading
```

No other definitions and no comments other than the module doc and the docstrings above (fill in the module doc's reader/sources/method).

Compile the file with `export PATH=$HOME/.elan/bin:$PATH; cd /home/claude/formalization; timeout 300 lake env lean runs/2026-11-09T1028Z/fsn_reader/SecondReadingFSNeg.lean`. Do not run `lake build`. Another build is running on the machine; that is expected, do not stop it. Do not commit.

Finally report: your general-m equation, BETA, A, C, D; the two kinds of decay at the edge and the behaviour of q / (D − p) for each; which kind satisfies the condition of job 2; your symbolic and numerical checks; what you consulted; anything uncertain.
