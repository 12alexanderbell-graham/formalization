# Blind literal reading brief (run 2026-11-26T1028Z): indices and limits of the geometrically shrinking bounds on the radial Gelfand turning-point quotients

Do NOT read anything in the repository except this brief (no `Checked/`, `Work/`, other `runs/` folders, other `*.md` files, git history). Write only to `runs/2026-11-26T1028Z/decay_reader/`. Do not compile Lean. You may run your own Python in a temporary directory outside the repository. arXiv: arxiv.org/pdf only, never ar5iv or e-print.

Mathematics: the Gelfand (Liouville–Bratu) problem Δu + λ e^u = 0 in the unit ball of R³, through its radial solution branch. Let w be the regular solution of w'' + (2/s) w' + e^w = 0, w(0) = 0 (the isothermal sphere equation). Rescaling w to the unit ball, the radial branch is parametrised by s with branch parameter λ(s) = s^P e^{w(s)}, with an integer P to be determined by you. As s grows, λ(s) rises to a first maximum, then oscillates with turning points of alternating type (maximum, minimum, maximum, …) and tends to the value G of the singular solution w = log(2/s²) (G an integer to be determined by you from that solution). The turning points are numbered as one sequence ζ indexed by the natural numbers 0, 1, 2, …, in increasing order of radius, starting with the first maximum (ζ 0).

Asymptotically the quotient of consecutive turning radii tends to exp(X π / √Y) and the quotient of consecutive deviations of λ from the singular value tends to −exp(−(π / √Y)), with natural numbers X, Y to be determined by you (from the linearisation of the isothermal equation about the singular solution, e.g. in the homology-invariant variables).

The claims being checked, for every natural number n (n = 0, 1, 2, …), with constants `c₁`, `c₂` and a ratio `q` left as variables:
1. The absolute difference between the quotient of the radius of the EIGHTH-plus-n turning point over the radius of the SEVENTH-plus-n turning point (counting the first maximum as the first turning point; so for n = 0, the eighth over the seventh) and its limit is at most `c₁` times `q` to the power n.
2. The absolute difference between the deviation quotient (the deviation of λ from the singular value at the eighth-plus-n turning point, divided by the deviation at the seventh-plus-n turning point) and its limit is at most `c₂` times `q` to the power n.

Fill in the capital placeholders in this Lean template — keep every other character, including the import lines, the doc comments and the line breaks, exactly as written — and write it to `runs/2026-11-26T1028Z/decay_reader/SecondReadingGelfandTurnDecay.lean`:

```lean
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
/-! Blind literal reading for geometrically shrinking bounds on the quotients of consecutive turning points of the radial Gelfand branch (run 2026-11-26T1028Z). -/
namespace Checked.Trust.SecondReading
/-- Radial Gelfand problem: the distance of the quotient of consecutive turning radii from its limit, at the seventh-plus-n turning point, is at most `c₁` times `q` to the power n. -/
def gelfandDecayRadiusBound (ζ : ℕ → ℝ) (n : ℕ) (c₁ q : ℝ) : Prop :=
  |ζ (n + A) / ζ (n + B) - Real.exp (X * Real.pi / Real.sqrt Y)| ≤ c₁ * q ^ n
/-- Radial Gelfand problem: the distance of the quotient of the deviations of the branch parameter from the singular value at consecutive turning points from its limit, at the seventh-plus-n turning point, is at most `c₂` times `q` to the power n. -/
def gelfandDecayDevBound (w : ℝ → ℝ) (ζ : ℕ → ℝ) (n : ℕ) (c₂ q : ℝ) : Prop :=
  |(ζ (n + A) ^ P * Real.exp (w (ζ (n + A))) - G) / (ζ (n + B) ^ P * Real.exp (w (ζ (n + B))) - G) -
    -Real.exp (-(Real.pi / Real.sqrt Y))| ≤ c₂ * q ^ n
end Checked.Trust.SecondReading
```

- A: a natural-number literal, the index in ζ of the eighth turning point (so ζ (n + A) is the eighth-plus-n turning point).
- B: a natural-number literal, the index in ζ of the seventh turning point.
- X, Y: real literals (natural numbers) of the limits as above.
- P: a natural-number literal, the power of s in λ.
- G: a real literal (an integer), the value of λ along the singular solution.

Also write `notes.md` in the same folder: your reasoning in a few lines and anything you were unsure of. Report both files' contents in your final message.
