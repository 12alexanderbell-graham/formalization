#!/usr/bin/env python3
"""Run 2026-11-19T1828Z: port the suction stacks Checked/Suction/{HS,HmS}{Flow,Limit,Assemble}.lean (start
(a0, 0, α)) to a start (a0, b0, α) with a wall velocity 0 ≤ b0 < 1, by exact replacements, each asserted (the
pattern of runs/2026-11-11T2228Z/scripts/port_suction_all.py). Used for the necessity witnesses of the wall
velocity p(0) = 0 in the monotone Hiemenz and Homann window headlines.
usage: port_wallvel.py STACK A0 B0 LO HI      (STACK in hiemenz homann; decimals as written in Lean)
Writes Checked/Trust/<T>Flow.lean, <T>Limit.lean, <T>Assemble.lean (T = HzG or HmG); the chains <T>UData,
<T>OData come from gen_hiemenz_wc_sp.py / gen_k_wc_sp.py + emit_wc_g.py."""
import re, sys
R = '/home/claude/formalization/'
STACKS = {'hiemenz': ('HS', 'HzG', 'Checked.Hiemenz', 'HEx', 'Hiemenz', '0.5', '1.5', '1.6'),
          'homann': ('HmS', 'HmG', 'Checked.Homann', 'HmEx', 'Homann', '0.1', None, None)}
st, A0, B0, LO, HI = sys.argv[1:6]
S, T, NS, P, NAME, SA0, _, _ = STACKS[st]
def rep(s, old, new, n=1):
    c = s.count(old)
    assert c == n, (old, c)
    return s.replace(old, new)
def resub(s, pat, new, n=None):
    r, c = re.subn(pat, new, s, flags=re.S)
    assert c >= 1 if n is None else c == n, (pat, c)
    return r
# ---- Flow
s = open(R + f'Checked/Suction/{S}Flow.lean').read()
s = rep(s, f'namespace Checked.Suction.{S}Flow', f'namespace Checked.Trust.{T}Flow')
s = rep(s, f'end Checked.Suction.{S}Flow', f'end Checked.Trust.{T}Flow')
s = resub(s, r'/-! .*? -/', f'/-! Necessity witnesses for the wall velocity, `{T}Flow`: the clamped {NAME} flow started from a wall value of f and a wall velocity, with a free wall shear; continuity in the wall shear. Ported by `runs/2026-11-19T1828Z/scripts/port_wallvel.py` from the suction module of the same stack. -/', 1)
s = resub(s, r'\b(local_sol|exists_sol|flow)S\b', r'\1G')
s = resub(s, r'\b(flowS_zero|flowS_deriv|flowS_cont)\b', lambda m: m.group(1).replace('flowS', 'flowG'))
s = resub(s, r'\b(local_solG|exists_solG|flowG|flowG_deriv|flowG_zero|flowG_cont) a0\b', r'\1 a0 b0')
s = s.replace('(a0 α T : ℝ)', '(a0 b0 α T : ℝ)').replace('(a0 α : ℝ)', '(a0 b0 α : ℝ)').replace('(a0 : ℝ) (T : ℝ)', '(a0 b0 : ℝ) (T : ℝ)')
s = resub(s, r'\(a0, 0, α\)', '(a0, b0, α)')
s = rep(s, '(a0, (0 : ℝ), α)', '(a0, b0, α)')
s = s.replace('from (a0, b0, α). -/', 'from (a0, b0, α). -/')
assert 'flowS' not in s and 'solS' not in s
open(R + f'Checked/Trust/{T}Flow.lean', 'w').write(s)
# ---- Limit
s = open(R + f'Checked/Suction/{S}Limit.lean').read()
s = rep(s, f'namespace Checked.Suction.{S}Limit', f'namespace Checked.Trust.{T}Limit')
s = rep(s, f'end Checked.Suction.{S}Limit', f'end Checked.Trust.{T}Limit')
s = resub(s, r'/-! .*? -/', f'/-! Necessity witnesses for the wall velocity, `{T}Limit`: a solution of the clamped {NAME} field from a wall value 0 ≤ f(0) ≤ 2 and a wall velocity 0 ≤ p(0) < 1 with neither shooting event solves the {NAME} problem with 0 ≤ p < 1, q > 0 and p tending to one. Ported by `runs/2026-11-19T1828Z/scripts/port_wallvel.py` from the suction module of the same stack. -/', 1)
s = rep(s, 'theorem no_eventS {a0 α : ℝ} (ha0 : 0 ≤ a0) (ha2 : a0 ≤ 2) (hα0 : 0 < α) (hα2 : α < 2) (Y : ℝ → ℝ × ℝ × ℝ)\n    (h0 : Y 0 = (a0, 0, α))',
        'theorem no_eventG {a0 b0 α : ℝ} (ha0 : 0 ≤ a0) (ha2 : a0 ≤ 2) (hb0 : 0 ≤ b0) (hb1 : b0 < 1)\n    (hα0 : 0 < α) (hα2 : α < 2) (Y : ℝ → ℝ × ℝ × ℝ)\n    (h0 : Y 0 = (a0, b0, α))')
s = rep(s, 'have p0 : (Y 0).2.1 = 0 := by rw [h0]', 'have p0 : (Y 0).2.1 = b0 := by rw [h0]')
s = rep(s, 'exfalso; apply notG; rw [← h, p0, q0]; exact ⟨by norm_num, hα0⟩', 'exfalso; apply notG; rw [← h, p0, q0]; exact ⟨hb1, hα0⟩')
s = rep(s, 'rw [p0] at h1; exact h1', 'rw [p0] at h1; linarith', 2)
s = rep(s, '      simp only [hZ, p0] at h2\n      norm_num at h2', '      simp only [hZ, p0] at h2\n      linarith')
open(R + f'Checked/Trust/{T}Limit.lean', 'w').write(s)
# ---- Assemble
s = open(R + f'Checked/Suction/{S}Assemble.lean').read()
s = rep(s, f'namespace Checked.Suction.{S}Assemble', f'namespace Checked.Trust.{T}Assemble')
s = rep(s, f'end Checked.Suction.{S}Assemble', f'end Checked.Trust.{T}Assemble')
s = rep(s, f'Checked.Suction.{S}Flow\n', f'Checked.Trust.{T}Flow\n', 2)
s = rep(s, f'import Checked.Suction.{S}Limit', f'import Checked.Trust.{T}Limit')
s = rep(s, f'import Checked.Suction.{S}UData', f'import Checked.Trust.{T}UData')
s = rep(s, f'import Checked.Suction.{S}OData', f'import Checked.Trust.{T}OData')
s = resub(s, r'/-! .*? -/', f'/-! Necessity witnesses for the wall velocity, `{T}Assemble`: the supremum argument for the {NAME} boundary-value problem with a nonzero wall velocity: a wall shear between the two certified shooting values with neither event, hence a solution with velocity in [0, 1), positive shear and velocity tending to one, whose wall shear lies in the interval printed in the statement of `exists_bvpG`. Ported by `runs/2026-11-19T1828Z/scripts/port_wallvel.py` from the suction module of the same stack. -/', 1)
m = re.search(r'set lo : ℝ := ([0-9.]+) with hlo\n  set hi : ℝ := ([0-9.]+) with hhi', s)
olo, ohi = m.group(1), m.group(2)
s = rep(s, f'theorem under_lo : Under ((flowS {SA0}) {olo}) :=\n  Checked.Suction.{S}UData.chainC (deriv_Icc _) (flowS_zero {SA0} _)',
        f'theorem under_lo : Under ((flowG {A0} {B0}) {LO}) :=\n  Checked.Trust.{T}UData.chainC (deriv_Icc _) (flowG_zero {A0} {B0} _)')
s = rep(s, f'theorem over_hi : Over ((flowS {SA0}) {ohi}) :=\n  Checked.Suction.{S}OData.chainC (deriv_Icc _) (flowS_zero {SA0} _)',
        f'theorem over_hi : Over ((flowG {A0} {B0}) {HI}) :=\n  Checked.Trust.{T}OData.chainC (deriv_Icc _) (flowG_zero {A0} {B0} _)')
s = resub(s, rf'/-- The {NAME} boundary-value problem with suction f\(0\) = [0-9./]+ has a solution with 0 ≤ p < 1,\nq > 0 and wall shear strictly between [0-9.]+ and [0-9.]+\. -/\ntheorem exists_bvpS :',
          f'/-- The {NAME} boundary-value problem with f(0) = {A0} and p(0) = {B0} has a solution with 0 ≤ p < 1,\nq > 0 and wall shear strictly between {LO} and {HI}. -/\ntheorem exists_bvpG :', 1)
s = rep(s, f'    f 0 = {SA0} ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧\n    {olo} < q 0 ∧ q 0 < {ohi} ∧',
        f'    f 0 = {A0} ∧ p 0 = {B0} ∧ Tendsto p atTop (𝓝 1) ∧\n    {LO} < q 0 ∧ q 0 < {HI} ∧')
s = rep(s, f'  set lo : ℝ := {olo} with hlo\n  set hi : ℝ := {ohi} with hhi', f'  set lo : ℝ := {LO} with hlo\n  set hi : ℝ := {HI} with hhi')
s = rep(s, f'Checked.Suction.{S}Limit.no_eventS (by norm_num) (by norm_num) ha0 ha2',
        f'Checked.Trust.{T}Limit.no_eventG (by norm_num) (by norm_num) (by norm_num) (by norm_num) ha0 ha2')
s = resub(s, rf'\bflowS_(zero|deriv|cont) {re.escape(SA0)}\b', rf'flowG_\1 {A0} {B0}')
s = resub(s, rf'\(flowS {re.escape(SA0)}\)', f'(flowG {A0} {B0})')
s = rep(s, f'simp [flowG_zero {A0} {B0}]', 'simp only [flowG_zero]', 3)
assert 'flowS' not in s and 'Suction' not in s, [l for l in s.split('\n') if 'flowS' in l or 'Suction' in l][:3]
open(R + f'Checked/Trust/{T}Assemble.lean', 'w').write(s)
print('ok', T)
