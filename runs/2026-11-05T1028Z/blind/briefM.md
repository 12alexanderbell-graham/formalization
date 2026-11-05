# Blind second formulation M (data: Moresco et al. 2016 fit statistics) — run 2026-11-05T1028Z

You write, from your own knowledge and derivation, Lean 4 definitions of three named quantities.
Another program wrote definitions with the same names; a machine will check (by unfolding and
`ring`/`simp`) whether yours equal theirs. You must NOT read theirs.

**Do not read** anything under /home/claude/formalization/Checked, /home/claude/formalization/Work,
/home/claude/formalization/runs (except this brief), /home/claude/formalization/scripts, or any `*.md`
file of the repository. Do not grep the repository for these names. Do not download anything (no web).
You may use Python/sympy (scratch files under /tmp/blindM/), and the Lean toolchain:
`cd /home/claude/formalization && export PATH=$HOME/.elan/bin:$PATH && lake env lean /tmp/blindM/X.lean`
compiles a file that imports Mathlib modules (a background build is running, so a compile may be slow).

The data table you must use is `Checked.Trust.SecondReading.m16Table : Fin 30 → ℝ × ℝ × ℝ`; row i is
`(z_i, H_i, σ_i) = ((m16Table i).1, (m16Table i).2.1, (m16Table i).2.2)`: redshift, measured Hubble
rate H(z) in km/s/Mpc, its standard deviation (uncorrelated Gaussian errors). For compiling, a stub of
that module is at /tmp/claude-0/-home-claude-formalization/98ad8e2c-5b4a-5da0-af5d-a469439edd02/scratchpad/blindM/SecondReadingM16.lean: copy it to /tmp/blindM/ and paste its namespace block at
the top of your scratch test file (your FINAL file must not contain the table; it imports
`Checked.Trust.SecondReadingM16`).

Write exactly one file: /home/claude/formalization/runs/2026-11-05T1028Z/blind/SecondFormulationM16.lean
with header

```lean
import Checked.Trust.SecondReadingM16
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Fin
namespace Checked.Trust.SecondFormulation
```

(adjust Mathlib imports if a name is missing; never `import Mathlib` as a whole), ending with
`end Checked.Trust.SecondFormulation`. Each definition gets a docstring saying what it is and how
you derived it. Your final file must compile once the stub is the real module (test with the stub
pasted in). No `sorry`.

The names promise a physical meaning. Write what the NAMED QUANTITY IS (the standard textbook
definition). Where a natural convention choice exists, it is stated; follow it exactly.

## The three definitions (exact names, argument order, types)

1. `noncomputable def e2OL (Ωm ΩΛ z : ℝ) : ℝ` — the square E(z)² = (H(z)/H₀)² of the dimensionless
   expansion rate of the ΛCDM model WITH spatial curvature ("open ΛCDM": curvature allowed, its
   density fraction fixed by the closure relation of the three fractions), matter (dust) density
   fraction Ωm, cosmological-constant fraction ΩΛ, at redshift z. No radiation.
   Write it as a polynomial in (1 + z) (no square root).

2. `noncomputable def chiSqOL (H0 Ωm ΩΛ : ℝ) : ℝ` — the chi-square of the model law
   H(z) = H0 · √(e2OL Ωm ΩΛ z) (Lean's `Real.sqrt`, your own `e2OL`) against the thirty rows of
   `Checked.Trust.SecondReading.m16Table` (sum over `i : Fin 30`, standard Gaussian χ², no
   normalisation constants), PLUS the contribution of a Gaussian prior on H0 with mean 73 and
   standard deviation 2.4 (km/s/Mpc), entered as one more χ² term.

3. `noncomputable def chiSqLine (a b : ℝ) : ℝ` — the chi-square of the straight line f(z) = a + b·z
   fitted to the thirty values H_i/(1 + z_i) (the rescaled Hubble rate), each with standard deviation
   σ_i/(1 + z_i) (error propagated by the same rescaling), PLUS one more data point: f(0) measured as
   73 with standard deviation 2.4. Standard Gaussian χ², no normalisation constants.

Finish with a short report: the three definitions as you wrote them, and any choice you had to make
that the brief did not fix.
