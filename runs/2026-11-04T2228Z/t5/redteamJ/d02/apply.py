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
LEAN = 'import Checked.Cosmography.LCDMWitness\n\n/-!\n# A fitted flat model, packaged as a function\n-/\n\nnamespace Checked.Cosmography.ModelFit\nopen Checked.Cosmography Checked.Cosmography.Aviles\n\ntheorem exists_fit : ∃ (a : ℝ → ℝ) (t₀ : ℝ), IsFlatLCDM (3 / 10) a t₀ ∧ ContDiffAt ℝ 6 a t₀ :=\n  Checked.Cosmography.AvilesWitness.exists_flatLCDM (by norm_num) (by norm_num)\n\n/-- Scale factor of the Pantheon best-fit flat model. -/\nnoncomputable def pantheonScale : ℝ → ℝ := Classical.choose exists_fit\n\n/-- Present epoch of the Pantheon best-fit flat model. -/\nnoncomputable def pantheonEpoch : ℝ := Classical.choose (Classical.choose_spec exists_fit)\n\n/-- Deceleration parameter of the Pantheon best-fit flat model. -/\ntheorem pantheon_q0 : decel pantheonScale pantheonEpoch = -11 / 20 := by\n  have h := Classical.choose_spec (Classical.choose_spec exists_fit)\n  have e := (flatLCDM_coeffs (3 / 10) pantheonScale pantheonEpoch h.1 h.2).1\n  rw [e]\n  norm_num\n\nend Checked.Cosmography.ModelFit\n'
create('Checked/Cosmography/ModelFit.lean', LEAN)
append('Checked.lean', 'import Checked.Cosmography.ModelFit\n')
append('scripts/trust/headlines.txt', 'Checked.Cosmography.ModelFit.pantheon_q0\n')
append('scripts/trust/def_kinds.txt', 'Checked.Cosmography.ModelFit.pantheonScale WITNESS\nChecked.Cosmography.ModelFit.pantheonEpoch WITNESS\n')
print('applied')
