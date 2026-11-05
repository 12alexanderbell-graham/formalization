# Blind second formulation A (chemistry, data) — run 2026-11-05T0828Z

You write, from your own knowledge and derivation, Lean 4 definitions of five named quantities.
Another program wrote definitions with the same names; a machine will check (by unfolding and
`ring`/`simp`) whether yours equal theirs. You must NOT read theirs.

**Do not read** anything under `/home/claude/formalization/Checked`, `/home/claude/formalization/Work`,
`/home/claude/formalization/runs` (except this brief), `/home/claude/formalization/scripts`, or any
`*.md` file of the repository. Do not grep the repository for these names. You may use Python/sympy
(write scratch files under `/tmp/blindA/`), and the Lean toolchain (`cd /home/claude/formalization &&
source ~/.elan/env && lake env lean /tmp/blindA/X.lean` compiles a file that imports only Mathlib;
a background build is running, so a compile may be slow — that is fine).

Write exactly one file: `/home/claude/formalization/runs/2026-11-05T0828Z/blind/SecondFormulationChem.lean`
with header

```lean
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
namespace Checked.Trust.SecondFormulation
```

(adjust Mathlib imports if a name is missing; never `import Mathlib` as a whole), ending with
`end Checked.Trust.SecondFormulation`. Each definition gets a docstring saying what it is and how you
derived it. The file must compile with no `sorry`.

The point of the exercise: the names below promise a physical meaning. Write what the NAMED
QUANTITY IS (the standard textbook definition), derived by you. Where a natural normalisation
choice exists, the convention to use is stated; follow it exactly.

## The five definitions (exact names, argument order and types)

1. `noncomputable def cubicP (R a b u w T v : ℝ) : ℝ` — the pressure of the generalized
   two-parameter cubic equation of state, the family that contains van der Waals (u = 0, w = 0),
   Redlich–Kwong with constant a (u = 1, w = 0) and Peng–Robinson with constant a (u = 2, w = −1),
   with u, w the coefficients in the attraction denominator in the standard textbook form
   (attraction term with denominator v² + u·b·v + w·b²). R gas constant, a attraction parameter,
   b co-volume, T temperature, v molar volume.

2. `def critCubic (u w x : ℝ) : ℝ` — for the equation of state of item 1, the critical point
   (∂P/∂v)_T = 0 and (∂²P/∂v²)_T = 0 determines x = v_c/b as a root of a cubic polynomial in x with
   coefficients depending only on u, w. Derive it yourself (sympy: eliminate T and a). Normalisation:
   the MONIC polynomial (coefficient of x³ equal to 1). Check: for van der Waals (u = w = 0) the
   root must be x = 3.

3. `noncomputable def acentric (ps pc : ℝ) : ℝ` — Pitzer's acentric factor ω, given `ps` the
   saturation (vapour) pressure at reduced temperature T/T_c = 0.7 and `pc` the critical pressure.

4. `noncomputable def chiSqHz {n : ℕ} (tbl : Fin n → ℝ × ℝ × ℝ) (H₀ Ω : ℝ) : ℝ` — the chi-square
   of the spatially flat ΛCDM expansion law with matter fraction Ω (matter + cosmological constant,
   no radiation; Hubble constant H₀) against a table of measurements, row i being
   `(z_i, H_i, σ_i) = ((tbl i).1, (tbl i).2.1, (tbl i).2.2)`: redshift, measured H(z), its standard
   deviation. Uncorrelated Gaussian errors. Use Lean's `√` (Real.sqrt) for the square root.

5. `noncomputable def margChiSq {n : ℕ} (tbl : Fin n → ℝ × ℝ × ℝ) (Hbar σ Ω : ℝ) : ℝ` — the
   "marginalised chi-square" of item 4 over H₀: minus two times the natural logarithm of the
   marginal likelihood, where the likelihood of (H₀, Ω) is exp(−χ²/2) with χ² = `chiSqHz tbl H₀ Ω`
   (no further normalisation), H₀ is integrated over ALL real numbers (Lebesgue integral,
   `∫ H₀ : ℝ, …`), against a NORMALISED Gaussian prior density on H₀ with mean `Hbar` and standard
   deviation `σ`. Write it with your own `chiSqHz` (refer to it as `chiSqHz`).

At the end, reply with: the file path, any item where you were unsure of the convention and what
you chose, and anything in the definitions above you believe is physically questionable.
