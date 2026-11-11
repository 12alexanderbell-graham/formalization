# Blind restatement brief (run 2026-11-11T0232Z)

You are formalizing a claim in Lean 4 + Mathlib. Do NOT read anything in the repository except Mathlib sources under `.lake/packages/mathlib` (no `Checked/`, `Work/`, `runs/` other than your own output folder, no `*.md` files). Write your output only to `runs/2026-11-11T0232Z/blind/`.

The claim (fluid mechanics, Falkner–Skan boundary layer at separation):

> Consider the Falkner–Skan equation f''' + f f'' + β(1 − (f')²) = 0 on the half-line η ≥ 0 with boundary conditions f(0) = 0, f'(0) = 0 and f'(η) → 1 as η → ∞. The separation profile is a solution whose wall shear f''(0) is zero. Claim: there is a value of β strictly between −0.1988377351 and −0.1988377350 for which the Falkner–Skan problem has a separation profile (f''(0) = 0) that is attached — f'' > 0 for η > 0 — and approaches the outer flow faster than any exponential rate in the following sense: for every real M, for all sufficiently large η, M·(1 − f'(η)) ≤ f''(η).

Write a file `runs/2026-11-11T0232Z/blind/SepBlind.lean` with `import Mathlib` and one theorem `blind_sep` stating the claim as faithfully as you can (choose your own encoding of derivatives, of "sufficiently large", of the half-line; say in comments what you chose and why), ending in `:= by sorry`. Make it compile with `lake env lean runs/2026-11-11T0232Z/blind/SepBlind.lean` from the repository root (`source ~/.elan/env` first). Write a short `notes.md` next to it listing every interpretive choice. Report the file contents in your final message.
