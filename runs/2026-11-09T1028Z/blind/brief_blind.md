# Brief: blind restatement of one claim (run 2026-11-09T1028Z)

You are an independent formalizer. Do not read anything in /home/claude/formalization except this brief and your output path; never open `Checked/`, `Work/`, `_archive/`, `runs/` (other than this folder), `scripts/`, `validation/`, `.lake/`, any `*.md` there, and do not use git history.

## The claim (in words)

Falkner–Skan equation with pressure-gradient parameter β = −1/10:

  f''' + f f'' + β (1 − (f')²) = 0   for η ≥ 0,

with boundary conditions f(0) = 0, f'(0) = 0 and f'(η) → 1 as η → ∞. Derivatives at η = 0 are one-sided (from the right).

**Claim.** There are two solutions of this boundary-value problem, each with f'' > 0 and 0 ≤ f' ≤ 1 on the whole half-line η ≥ 0, such that neither of them has the property "for every real number M, for all sufficiently large η, M · (1 − f'(η)) ≤ f''(η)", and whose wall values f''(0) are different.

## What to write

ONE Lean 4 file `runs/2026-11-09T1028Z/blind/NegOutsideBlind.lean`, `import Mathlib`, namespace `Blind.NegOutside`, containing your own definition(s) of what a solution is and ONE theorem `two_outside` stating the claim, proved by `sorry`. Choose the formulation you think is faithful to the words; write in a `notes.md` next to it every interpretation choice you made (one line each). Compile with `export PATH=$HOME/.elan/bin:$PATH; cd /home/claude/formalization; timeout 900 lake env lean runs/2026-11-09T1028Z/blind/NegOutsideBlind.lean` (the only expected warning is the `sorry`). Do not run `lake build`; another build may be running on the machine, do not stop it. Do not commit. Report your statement and notes.
