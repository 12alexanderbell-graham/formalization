# Blind restatement brief (run 2026-11-11T0828Z)

You are formalizing a claim in Lean 4 + Mathlib. Do NOT read anything in the repository /home/claude/formalization (no `Checked/`, `Work/`, `runs/` other than your own output folder, no `*.md` files, no git history). Write your output only to `runs/2026-11-11T0828Z/blind/`. Lean is not installed on this machine: do not try to install or compile; write carefully against current Mathlib names (`HasDerivWithinAt`, `derivWithin`, `ContDiffOn`, `Filter.Tendsto`, `Filter.atTop`, `Set.Ici`, `∀ᶠ … in …`).

The claim (fluid mechanics, Falkner–Skan boundary layer at separation):

> Consider the Falkner–Skan equation f''' + f f'' + β(1 − (f')²) = 0 on the half-line η ≥ 0 with f(0) = 0, f'(0) = 0 and f'(η) → 1 as η → ∞. Call a solution a separation profile if its wall shear f''(0) is zero, f'' > 0 for η > 0, and it approaches the outer flow faster than any exponential rate in the sense: for every real M, for all sufficiently large η, M·(1 − f'(η)) ≤ f''(η). Two papers print β = −0.1988376 as the parameter value of the solution with zero wall shear. Claim: there is no separation profile with β = −0.1988376.

Write `runs/2026-11-11T0828Z/blind/SepPrintedBlind.lean` (`import Mathlib`, any definitions you need, one theorem `blind_sep_printed` stating the claim as faithfully as you can, `:= by sorry`) and a short `notes.md` listing every interpretive choice. Report the file contents in your final message.
