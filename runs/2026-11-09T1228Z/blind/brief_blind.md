# Brief: blind restatement of two claims (run 2026-11-09T1228Z)

You are an independent formalizer. Do not read anything in /home/claude/formalization except this brief and your output path; never open `Checked/`, `Work/`, `_archive/`, `runs/` (other than this folder), `scripts/`, `validation/`, `.lake/`, any `*.md` there, and do not use git history.

## The claims (in words)

Falkner–Skan equation with pressure-gradient parameter β = −1/10:

  f''' + f f'' + β (1 − (f')²) = 0   for η ≥ 0,

with boundary conditions f(0) = 0, f'(0) = 0 and f'(η) → 1 as η → ∞. Derivatives at η = 0 are one-sided (from the right).

**Claim 1.** Every solution of this boundary-value problem with f'' > 0 on the whole half-line η ≥ 0 and with the property "for every real number M, for all sufficiently large η, M · (1 − f'(η)) ≤ f''(η)" has 0.3192697598 < f''(0) < 0.3192697599.

**Claim 2.** Every solution of this boundary-value problem with f'' > 0 on the whole half-line η ≥ 0 (no condition on how f' approaches 1) has f''(0) < 0.3192697599.

## What to write

ONE Lean 4 file `runs/2026-11-09T1228Z/blind/NegWindowBlind.lean`, `import Mathlib`, namespace `Blind.NegWindow`, containing your own definition(s) of what a solution is and TWO theorems `window` (Claim 1) and `monotone_lt` (Claim 2), proved by `sorry`. Choose the formulation you think is faithful to the words; write in a `notes.md` next to it every interpretation choice you made (one line each). Compile with `export PATH=$HOME/.elan/bin:$PATH; cd /home/claude/formalization; timeout 900 lake env lean runs/2026-11-09T1228Z/blind/NegWindowBlind.lean` (the only expected warnings are the `sorry`s). Do not run `lake build`; another build may be running on the machine, do not stop it. Do not commit. Report your statements and notes.
