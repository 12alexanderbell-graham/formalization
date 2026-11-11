# Blind restatement brief (run 2026-11-11T1028Z)

You are formalizing two claims in Lean 4 + Mathlib. Do NOT read anything in the repository /home/claude/formalization (no `Checked/`, `Work/`, `runs/` other than your own output folder, no `*.md` files, no git history). Write your output only to `runs/2026-11-11T1028Z/blind/`. Do not compile (another job is using the machine's memory); write carefully against current Mathlib names (`HasDerivWithinAt`, `derivWithin`, `ContDiffOn`, `Filter.Tendsto`, `Filter.atTop`, `Set.Ici`, `∀ᶠ … in …`).

The claims (fluid mechanics, Falkner–Skan boundary layer with an adverse pressure gradient):

> Consider the Falkner–Skan equation f''' + f f'' + β(1 − (f')²) = 0 on the half-line η ≥ 0 with β = −0.1988, boundary conditions f(0) = 0, f'(0) = 0 and f'(η) → 1 as η → ∞. Call a solution attached if f''(η) > 0 for every η ≥ 0, and say it approaches the outer flow faster than any exponential rate if for every real M, for all sufficiently large η, M·(1 − f'(η)) ≤ f''(η).
> Claim 1: every attached solution that approaches the outer flow faster than any exponential rate has wall shear f''(0) strictly between 0.0052181 and 0.0052182.
> Claim 2: an attached solution that approaches the outer flow faster than any exponential rate exists.

Write `runs/2026-11-11T1028Z/blind/Neg1988Blind.lean` (`import Mathlib`, any definitions you need, two theorems `blind_neg1988_window` and `blind_neg1988_exists` stating the claims as faithfully as you can, each `:= by sorry`) and a short `notes.md` listing every interpretive choice. Report the file contents in your final message.
