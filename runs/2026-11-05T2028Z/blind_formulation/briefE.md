# Blind second formulation E (run 2026-11-05T2028Z)

You write, from your own knowledge, one Lean 4 definition. Another program wrote a definition with
the same name; a machine will check whether yours equals theirs (as functions of all arguments).
You must NOT read theirs.

**Do not read** anything under `/home/claude/formalization/Checked`, `/home/claude/formalization/Work`,
`/home/claude/formalization/runs` (except this brief), `/home/claude/formalization/scripts`, or any
`*.md`/`*.txt` file of the repository; do not grep the repository. You MAY import
`Checked.Trust.SecondFormulation` (without opening it): it provides
`Checked.Trust.SecondFormulation.chiSqHz {n : ℕ} (tbl : Fin n → ℝ × ℝ × ℝ) (H₀ Ω : ℝ) : ℝ`, the chi-square of
the spatially flat ΛCDM law against the table (row i = (z_i, H_i, σ_i)). Compile with
`cd /home/claude/formalization && PATH=$HOME/.elan/bin:$PATH lake env lean /tmp/blindE/X.lean`
(a background build may be running; never run `lake build`).

Write exactly one file: `/home/claude/formalization/runs/2026-11-05T2028Z/blind_formulation/SecondFormulationE.lean`
```lean
import Checked.Trust.SecondFormulation
namespace Checked.Trust.SecondFormulationE
... your definition, with a docstring ...
end Checked.Trust.SecondFormulationE
```

`noncomputable def margChiSq {n : ℕ} (tbl : Fin n → ℝ × ℝ × ℝ) (Hbar σ Ω : ℝ) : ℝ` — the
"marginalised chi-square" over H₀: minus two times the natural logarithm of the marginal likelihood,
where the likelihood of (H₀, Ω) is exp(−χ²/2) with χ² = `Checked.Trust.SecondFormulation.chiSqHz tbl H₀ Ω`
(no further normalisation), H₀ is integrated over ALL real numbers (Lebesgue integral, `∫ H₀ : ℝ, …`),
against a NORMALISED Gaussian prior density on H₀ with mean `Hbar` whose standard deviation is |σ|
(the argument σ may be given with either sign; the density must be a correct normalised density for
every real σ ≠ 0). Use `Real.exp`, `Real.log`, `Real.pi`, `Real.sqrt` or `|·|` as you see fit.

Reply with the file path and the formula in plain text.
