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
LEAN = "import Checked.Chemistry.CubicEOS\nimport Checked.Trust.NonVacuity\n\n/-!\n# Redlich–Kwong attraction constant with a decimal-place tolerance\n-/\n\nnamespace Checked.Chemistry.LooseDigits\nopen Checked.Chemistry.CubicEOS Checked.Records\n\n/-- `x` rounds to `d` at `k` decimal places, with the half-unit tolerance of the last kept place. -/\ndef RoundsTo' (x d : ℝ) (k : ℕ) : Prop := |x - d| ≤ 1 / (2 * 10 ^ (k - 1))\n\n/-- Redlich–Kwong: the attraction constant rounds to the printed value at five decimal places. -/\ntheorem rk_omega_a_printed (R a b T v : ℝ) (ha : 0 < a) (hb : 0 < b) (hv : b < v)\n    (hc : IsCriticalIsotherm (cubicP R a b 1 0 T) v) :\n    RoundsTo' (a * cubicP R a b 1 0 T v / (R * T) ^ 2) 0.4275 5 := by\n  have h := (rk_constants R a b T v ha hb hv hc).2.2\n  unfold RoundsTo at h\n  unfold RoundsTo'\n  have e : (10 : ℝ) ^ (5 - 1) = 10000 := by norm_num\n  rw [e]\n  rw [abs_le] at h ⊢\n  obtain ⟨h1, h2⟩ := h\n  constructor <;> norm_num at h1 h2 ⊢ <;> linarith\n\nend Checked.Chemistry.LooseDigits\n\nnamespace Checked.Trust.NV\n\ntheorem rk_omega_a_printed : nonvacuity% Checked.Chemistry.LooseDigits.rk_omega_a_printed := by\n  obtain ⟨⟨T, v⟩, ⟨_, hv, hc⟩, -⟩ := Checked.Chemistry.CubicEOS.exists_unique_critical 1 1 1 1 0\n    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)\n  exact ⟨1, 1, 1, T, v, by norm_num, by norm_num, hv, hc, trivial⟩\n\nend Checked.Trust.NV\n"
create('Checked/Chemistry/LooseDigits.lean', LEAN)
append('Checked.lean', 'import Checked.Chemistry.LooseDigits\n')
append('scripts/trust/headlines.txt', 'Checked.Chemistry.LooseDigits.rk_omega_a_printed\n')
append('scripts/trust/def_kinds.txt', "Checked.Chemistry.LooseDigits.RoundsTo' MATH\n")
print('applied')
