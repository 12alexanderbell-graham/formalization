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
LEAN = 'import Checked.Cosmography.CPLExistence\nimport Checked.Trust.NonVacuity\n\n/-!\n# Jerk of a flat matter plus dark-energy model, in the notation of the CPL parametrisation\n-/\n\nnamespace Checked.Cosmography.CPLNames\nopen Checked.Cosmography Checked.Cosmography.CPL\n\n/-- Jerk of a flat matter plus dark-energy model with parametrisation `(Ω, wa, w0)`. -/\ntheorem jerk_cpl (Ω wa w0 : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (hL : IsFlatCPL Ω wa w0 a t₀)\n    (hs : ContDiffAt ℝ 5 a t₀) :\n    cosmoCoeff 3 a t₀ = 1 + 3 / 2 * (1 - Ω) * (3 * wa * (1 + wa) + w0) :=\n  (flatCPL_coeffs Ω wa w0 a t₀ hL hs).2.1\n\nend Checked.Cosmography.CPLNames\n\nnamespace Checked.Trust.NV\n\ntheorem jerk_cpl : nonvacuity% Checked.Cosmography.CPLNames.jerk_cpl := by\n  obtain ⟨a, hL, hs⟩ := Checked.Cosmography.CPLExistence.exists_flatCPL (1 / 2) (-1) 1\n  exact ⟨1 / 2, -1, 1, a, 0, hL, hs, trivial⟩\n\nend Checked.Trust.NV\n'
create('Checked/Cosmography/CPLNames.lean', LEAN)
append('Checked.lean', 'import Checked.Cosmography.CPLNames\n')
append('scripts/trust/headlines.txt', 'Checked.Cosmography.CPLNames.jerk_cpl\n')
append('scripts/trust/def_kinds.txt', '\n')
print('applied')
