# Blind restatement brief (run 2026-11-11T1228Z)

You are formalizing three claims in Lean 4 + Mathlib. Do NOT read anything in the repository /home/claude/formalization (no `Checked/`, `Work/`, `runs/` other than your own output folder, no `*.md` files, no git history). Write your output only to `runs/2026-11-11T1228Z/blind/`. Do not compile (other jobs are using the machine's memory); write carefully against current Mathlib names (`HasDerivWithinAt`, `derivWithin`, `ContDiffOn`, `Filter.Tendsto`, `Filter.atTop`, `Set.Ici`, `∀ᶠ … in …`).

The claims (fluid mechanics, Falkner–Skan boundary layer with an adverse pressure gradient):

> Consider the Falkner–Skan equation f''' + f f'' + β(1 − (f')²) = 0 on the half-line η ≥ 0 with β = −0.1988, boundary conditions f(0) = 0, f'(0) = 0 and f'(η) → 1 as η → ∞. Say a solution approaches the outer flow faster than any exponential rate if for every real M, for all sufficiently large η, M·(1 − f'(η)) ≤ f''(η).
> Claim 1: there is a solution with |f'| ≤ 1 on the half-line that approaches the outer flow faster than any exponential rate and has reversed flow at the wall: its wall shear f''(0) lies strictly between −0.00515743 and −0.00515741.
> Claim 2: if f solves the Falkner–Skan equation with β = −0.1988 on the half-line with f(0) = 0, f'(0) = 0 and f''(0) = −0.005158 (no condition at infinity), then f'(η) > 1 for some η > 0.
> Claim 3: there are two solutions with |f'| ≤ 1 on the half-line, both approaching the outer flow faster than any exponential rate, with different wall shears.

Write `runs/2026-11-11T1228Z/blind/Neg1988RevBlind.lean` (`import Mathlib`, any definitions you need, three theorems `blind_rev_window`, `blind_rev_printed`, `blind_rev_two` stating the claims as faithfully as you can, each `:= by sorry`) and a short `notes.md` listing every interpretive choice. Report the file contents in your final message.
