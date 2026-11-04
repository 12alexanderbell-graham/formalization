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
LEAN = 'import Mathlib.Data.Real.Basic\nimport Mathlib.Tactic.NormNum\nimport Mathlib.Tactic.Linarith\nimport Checked.Records.Basic\n\n/-!\n# Temperature scale of the van der Waals equation for carbon dioxide\n-/\n\nnamespace Checked.Chemistry.VdWScale\nopen Checked.Records\n\n/-- van der Waals temperature scale `8a/(27Rb)` with `R` in L·bar/(mol·K), `a` in L²·bar/mol², `b` in L/mol. -/\nnoncomputable def tempScale (a b : ℝ) : ℝ := 8 * a / (27 * 0.08134 * b)\n\n/-- Carbon dioxide, `a = 3.640` and `b = 0.04267`: the van der Waals temperature scale in kelvin,\nto the nearest unit. -/\ntheorem co2_scale : RoundsTo (tempScale 3.640 0.04267) 311 0 := by\n  unfold RoundsTo tempScale\n  rw [abs_le]\n  constructor <;> norm_num\n\nend Checked.Chemistry.VdWScale\n'
create('Checked/Chemistry/VdWScale.lean', LEAN)
append('Checked.lean', 'import Checked.Chemistry.VdWScale\n')
append('scripts/trust/headlines.txt', 'Checked.Chemistry.VdWScale.co2_scale\n')
append('scripts/trust/def_kinds.txt', 'Checked.Chemistry.VdWScale.tempScale FORMULA\n')
print('applied')
