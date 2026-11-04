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
LEAN = 'import Checked.Cosmography.LCDMWitness\nimport Checked.Trust.NonVacuity\n\n/-!\n# Deceleration parameter of a flat model in terms of the dark-energy fraction\n-/\n\nnamespace Checked.Cosmography.LambdaForm\nopen Checked.Cosmography Checked.Cosmography.Aviles\n\n/-- Deceleration parameter of a flat model in terms of the dark-energy fraction. -/\ntheorem q0_from_lambda (ΩΛ : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (hL : IsFlatLCDM ΩΛ a t₀)\n    (hs : ContDiffAt ℝ 6 a t₀) :\n    decel a t₀ = 3 / 2 * ΩΛ - 1 :=\n  (flatLCDM_coeffs ΩΛ a t₀ hL hs).1\n\nend Checked.Cosmography.LambdaForm\n\nnamespace Checked.Trust.NV\n\ntheorem q0_from_lambda : nonvacuity% Checked.Cosmography.LambdaForm.q0_from_lambda := by\n  obtain ⟨a, t₀, hL, hs⟩ := Checked.Cosmography.AvilesWitness.exists_flatLCDM (Ω := 1 / 2)\n    (by norm_num) (by norm_num)\n  exact ⟨1 / 2, a, t₀, hL, hs, trivial⟩\n\nend Checked.Trust.NV\n'
create('Checked/Cosmography/LambdaForm.lean', LEAN)
append('Checked.lean', 'import Checked.Cosmography.LambdaForm\n')
append('scripts/trust/headlines.txt', 'Checked.Cosmography.LambdaForm.q0_from_lambda\n')
append('scripts/trust/def_kinds.txt', '\n')
print('applied')
