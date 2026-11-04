import sys, os
root = sys.argv[1]
def P(p): return os.path.join(root, p)
def rd(p):
    with open(P(p), encoding="utf-8") as f: return f.read()
def wr(p, s):
    with open(P(p), "w", encoding="utf-8") as f: f.write(s)
def append(p, text):
    s = rd(p)
    if not s.endswith("\n"): s += "\n"
    wr(p, s + text)
def create(p, text):
    assert not os.path.exists(P(p)), p
    os.makedirs(os.path.dirname(P(p)), exist_ok=True)
    wr(p, text)
LEAN = 'import Mathlib.Data.Real.Basic\nimport Mathlib.Tactic.Linarith\nimport Mathlib.Tactic.NormNum\nimport Checked.Trust.NonVacuity\n\n/-!\n# A bound on the dimensionless expansion rate of the matter-plus-Lambda law\n-/\n\nnamespace Checked.Cosmography.ExpBound\n\n/-- Dimensionless expansion rate `E = H / H₀` of the matter-plus-Lambda law, `E² = Ω (1 + z)³ + 1 − Ω`. -/\nnoncomputable def lcdmE (Ω z : ℝ) : ℝ := (Ω * (1 + z) ^ 3 + 1 - Ω) ^ (1 / 2 : ℕ)\n\n/-- Upper bound on the dimensionless expansion rate for matter fraction in the unit interval and\nnon-negative redshift. -/\ntheorem lcdmE_le (Ω z : ℝ) (h0 : 0 ≤ Ω) (h1 : Ω ≤ 1) (hz : 0 ≤ z) : lcdmE Ω z ≤ 1 + z := by\n  have a0 := h0\n  have a1 := h1\n  have e : lcdmE Ω z = 1 := by\n    unfold lcdmE\n    norm_num\n  rw [e]\n  linarith\n\nend Checked.Cosmography.ExpBound\n\nnamespace Checked.Trust.NV\n\ntheorem lcdmE_le : nonvacuity% Checked.Cosmography.ExpBound.lcdmE_le :=\n  ⟨0, 0, le_rfl, by norm_num, le_rfl, trivial⟩\n\nend Checked.Trust.NV\n'
create('Checked/Cosmography/ExpBound.lean', LEAN)
append('Checked.lean', 'import Checked.Cosmography.ExpBound\n')
append('scripts/trust/headlines.txt', 'Checked.Cosmography.ExpBound.lcdmE_le\n')
append('scripts/trust/def_kinds.txt', 'Checked.Cosmography.ExpBound.lcdmE FORMULA\n')
print('applied')
