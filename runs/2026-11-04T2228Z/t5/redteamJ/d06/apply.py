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
LEAN = 'import Mathlib.Data.Real.Basic\nimport Mathlib.Tactic.FieldSimp\nimport Mathlib.Tactic.Ring\nimport Checked.Trust.NonVacuity\n\n/-!\n# Boyle temperature of the van der Waals gas in units of the temperature scale 8a/(27Rb)\n-/\n\nnamespace Checked.Chemistry.BoyleScale\n\n/-- Boyle temperature of the van der Waals gas with attraction `a`, co-volume `b`, gas constant `R`. -/\nnoncomputable def boyleT (a b R : ℝ) : ℝ := 2 * a / (R * b)\n\n/-- The van der Waals temperature scale `8a/(27Rb)`. -/\nnoncomputable def tcScale (a b R : ℝ) : ℝ := 8 * a / (27 * R * b)\n\n/-- Boyle temperature of the van der Waals gas in units of the scale `8a/(27Rb)`. -/\ntheorem boyle_over_scale (a b R : ℝ) (hR : R ≠ 0) (hb : b ≠ 0) :\n    boyleT a b R = 27 / 4 * tcScale a b R := by\n  have u1 := hR\n  have u2 := hb\n  unfold boyleT tcScale\n  first\n    | (field_simp; ring)\n    | field_simp\n\nend Checked.Chemistry.BoyleScale\n\nnamespace Checked.Trust.NV\n\ntheorem boyle_over_scale : nonvacuity% Checked.Chemistry.BoyleScale.boyle_over_scale :=\n  ⟨1, 1, 1, one_ne_zero, one_ne_zero, trivial⟩\n\nend Checked.Trust.NV\n'
create('Checked/Chemistry/BoyleScale.lean', LEAN)
append('Checked.lean', 'import Checked.Chemistry.BoyleScale\n')
append('scripts/trust/headlines.txt', 'Checked.Chemistry.BoyleScale.boyle_over_scale\n')
append('scripts/trust/def_kinds.txt', 'Checked.Chemistry.BoyleScale.boyleT FORMULA\nChecked.Chemistry.BoyleScale.tcScale FORMULA\n')
print('applied')
