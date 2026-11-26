# Blind literal reading brief (run 2026-11-26T0428Z): geometrically shrinking bounds on the Bonnor–Ebert extremum quotients

Do NOT read anything in the repository except this brief (no `Checked/`, `Work/`, other `runs/` folders, other `*.md` files, git history). Write only to `runs/2026-11-26T0428Z/decay_reader/`. Do not compile Lean. You may run your own Python in a temporary directory outside the repository. arXiv: arxiv.org/pdf only, never ar5iv or e-print.

Physics: the isothermal sphere. Let w be the regular solution of w'' + (2/s) w' + e^w = 0, w(0) = 0, with derivative φ = w' (so φ < 0 for s > 0). In these dimensionless units the pressure-confined (Bonnor–Ebert) mass inside radius s is m(s) = s^P (−φ(s)) e^{w(s)/D} / √(F π), with integers P, D, F to be determined by you from the standard definition (the mass is the integral of the density e^w over the ball of radius s, divided by the square root of the pressure e^w at s, with the normalisation by √(4π) of the Bonnor–Ebert literature — work it out so that the mass of the singular isothermal sphere w = log(2/s²) is a constant). m(s) rises to a first maximum, then oscillates with extrema of alternating type (maximum, minimum, maximum, …) and tends to the mass √(G / π) of the singular isothermal sphere (G an integer to be determined by you from that solution). The extrema are numbered as one sequence ξ indexed by the natural numbers 0, 1, 2, …, in increasing order of radius, starting with the first maximum (ξ 0).

Asymptotically the quotient of consecutive extremum radii tends to exp(X π / √Y) and the quotient of consecutive deviations of the mass from the singular value tends to −exp(−(π / √Y)), with natural numbers X, Y to be determined by you (from the linearisation of the isothermal equation about the singular solution, e.g. in the homology-invariant variables).

The claims being checked, for every natural number n (n = 0, 1, 2, …):
1. The absolute difference between the quotient of the radius of the SEVENTH-plus-n extremum over the radius of the SIXTH-plus-n extremum (counting the first maximum as the first extremum; so for n = 0, the seventh over the sixth) and its limit is at most twenty-three tenths times (twenty-one fiftieths) to the power n.
2. The absolute difference between the deviation quotient (the deviation of the mass from the singular value at the seventh-plus-n extremum, divided by the deviation at the sixth-plus-n extremum) and its limit is at most three twentieths times (twenty-one fiftieths) to the power n.

Fill in the capital placeholders in this Lean template — keep every other character, including the import lines, the `open` line, the doc comments and the line breaks, exactly as written — and write it to `runs/2026-11-26T0428Z/decay_reader/SecondReadingBETurnDecay.lean`:

```lean
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
/-! Blind literal reading for geometrically shrinking bounds on the quotients of consecutive extrema of the Bonnor–Ebert mass (run 2026-11-26T0428Z). -/
namespace Checked.Trust.SecondReading
/-- Bonnor–Ebert sphere: the distance of the quotient of consecutive extremum radii from its limit, at the sixth-plus-n extremum, is at most a constant times a power of a ratio. -/
def beDecayRadii (ξ : ℕ → ℝ) (n : ℕ) : Prop :=
  |ξ (n + A) / ξ (n + B) - Real.exp (X * Real.pi / Real.sqrt Y)| ≤ C1 / C2 * (Q1 / Q2) ^ n
/-- Bonnor–Ebert sphere: the distance of the quotient of the deviations of the pressure-confined mass from the singular value at consecutive extrema from its limit, at the sixth-plus-n extremum, is at most a constant times a power of a ratio. -/
def beDecayDev (w φ : ℝ → ℝ) (ξ : ℕ → ℝ) (n : ℕ) : Prop :=
  |(ξ (n + A) ^ P * (-φ (ξ (n + A))) * Real.exp (w (ξ (n + A)) / D) / Real.sqrt (F * Real.pi) -
        Real.sqrt (G / Real.pi)) /
      (ξ (n + B) ^ P * (-φ (ξ (n + B))) * Real.exp (w (ξ (n + B)) / D) / Real.sqrt (F * Real.pi) -
        Real.sqrt (G / Real.pi)) -
    -Real.exp (-(Real.pi / Real.sqrt Y))| ≤ E1 / E2 * (Q1 / Q2) ^ n
end Checked.Trust.SecondReading
```

- A: a natural-number literal, the index in ξ of the seventh extremum (so ξ (n + A) is the seventh-plus-n extremum).
- B: a natural-number literal, the index in ξ of the sixth extremum.
- X, Y: real literals (natural numbers) of the limits as above.
- C1, C2: natural-number literals with C1 / C2 the constant of claim 1, in lowest terms.
- E1, E2: natural-number literals with E1 / E2 the constant of claim 2, in lowest terms.
- Q1, Q2: natural-number literals with Q1 / Q2 the ratio of both claims, in lowest terms.
- P: a natural-number literal, the power of s in m.
- D: a real literal (an integer), the divisor of w in the exponent.
- F: a real literal (an integer), the factor of π under the square root of the normalisation.
- G: a real literal (an integer), with √(G/π) the mass of the singular isothermal sphere.

Also write `notes.md` in the same folder: your reasoning in a few lines and anything you were unsure of. Report both files' contents in your final message.
