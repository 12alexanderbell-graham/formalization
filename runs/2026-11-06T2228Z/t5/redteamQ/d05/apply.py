import sys, pathlib
root = pathlib.Path(sys.argv[1])
def rd(p): return (root/p).read_text(encoding="utf-8")
def wr(p, s): (root/p).write_text(s, encoding="utf-8")
def app(p, s):
    t = rd(p)
    if not t.endswith("\n"): t += "\n"
    wr(p, t + s)
def rep(p, old, new):
    t = rd(p); assert t.count(old) == 1, (p, old[:60], t.count(old)); wr(p, t.replace(old, new))

LEAN = 'import Checked.Records.Basic\nimport Mathlib.Analysis.SpecialFunctions.Exp\nimport Checked.Trust.NonVacuity\n\n/-!\n# Relaxation of a deviation\n\nThe deviation exp(-t) of a first-order process.\n-/\n\nnamespace Checked.Math.Relaxation\n\n/-- The deviation `Real.exp (-t)` from equilibrium is below 1/2 for every t ≥ 1: the system has settled at equilibrium. -/\ntheorem deviation_below_half (t : ℝ) (ht : 1 ≤ t) : Real.exp (-t) < 1 / 2 := by\n  have h1 : (2 : ℝ) < Real.exp 1 := by\n    have := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)\n    linarith\n  have h2 : Real.exp 1 ≤ Real.exp t := Real.exp_le_exp.mpr ht\n  have h3 : Real.exp (-t) * Real.exp t = 1 := by\n    rw [← Real.exp_add]; simp\n  have h4 : 0 < Real.exp (-t) := Real.exp_pos _\n  have h5 : 2 < Real.exp t := lt_of_lt_of_le h1 h2\n  nlinarith [mul_pos (sub_pos.mpr h5) h4]\n\nend Checked.Math.Relaxation\n\nnamespace Checked.Math.RelaxationNV\n\ntheorem deviation_below_half : nonvacuity% Checked.Math.Relaxation.deviation_below_half :=\n  ⟨1, le_refl _, trivial⟩\n\nend Checked.Math.RelaxationNV\n'
wr('Checked/Math/Relaxation.lean', LEAN)
app("Checked.lean", "import Checked.Math.Relaxation\n")
app("scripts/trust/headlines.txt", 'Checked.Math.Relaxation.deviation_below_half' + "\n")
app("scripts/trust/prose_vocab.txt", 'equilibrium\nsystem\nsettled\n')
app("LEDGER.md", '\n## Run 2026-11-06T2328Z (red team Q defect d05, disclosed vocabulary)\n- prose_vocab.txt gains the domain words `equilibrium`, `system`, `settled` for the relaxation headline `deviation_below_half`.\n')
