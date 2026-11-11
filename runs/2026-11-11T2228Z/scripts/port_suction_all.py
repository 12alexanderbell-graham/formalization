#!/usr/bin/env python3
"""Run 2026-11-11T2228Z: port a shooting stack (<NS>/<P>ExFlow.lean, <P>ExLimit.lean, <P>ExAssemble.lean of
Checked/Hiemenz (HEx), Checked/Homann (HmEx), Checked/FSFifth (F5Ex), Checked/FSTenth (F10Ex)) to a wall value
f(0) = a0 > 0 (suction) by exact replacements, each asserted (generalisation of port_suction.py).
usage: port_suction_all.py STACK A0 LO HI L     (STACK in hiemenz homann k5 k10; decimals as written in Lean)
Writes Work/Suction/<T>Flow.lean, <T>Limit.lean, <T>Assemble.lean; the chains <T>UData/<T>OData come from
gen_k_wc_s.py + emit_wc_s.py."""
import re, sys
R = '/home/claude/formalization/'
STACKS = {'hiemenz': ('Checked/Hiemenz', 'Checked.Hiemenz', 'HEx', 'HS', 'Hiemenz'),
          'homann': ('Checked/Homann', 'Checked.Homann', 'HmEx', 'HmS', 'Homann'),
          'k5': ('Checked/FSFifth', 'Checked.FSFifth', 'F5Ex', 'F5S', 'K = 5 (Falkner–Skan β = 1/5, scaled)'),
          'k10': ('Checked/FSTenth', 'Checked.FSTenth', 'F10Ex', 'F10S', 'K = 10 (Falkner–Skan β = 1/10, scaled)')}
st, A0, LO, HI, L = sys.argv[1:6]
D, NS, P, T, NAME = STACKS[st]
def rep(s, old, new, n=1):
    c = s.count(old)
    assert c == n, (old, c)
    return s.replace(old, new)
def resub(s, pat, new, n=1):
    r, c = re.subn(pat, new, s, flags=re.S)
    assert c == n, (pat, c)
    return r
HDR = """import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
"""
# ---- Flow
src = open(R + f'{D}/{P}Flow.lean').read()
a = src.index('/-- A solution on [0, T] for every T > 0. -/')
b = src.index('/-- Forward uniqueness on [0, T]. -/')
c = src.index('theorem exists_sol (α : ℝ)')
e = src.index(f'end {NS}.{P}Flow')
body = src[a:b] + src[c:e]
body = rep(body, 'theorem local_sol (α T : ℝ)', 'theorem local_solS (a0 α T : ℝ)')
body = rep(body, 'Y 0 = (0, 0, α)', 'Y 0 = (a0, 0, α)', 3)
body = rep(body, '((0 : ℝ), (0 : ℝ), α)', '(a0, (0 : ℝ), α)')
body = rep(body, 'theorem exists_sol (α : ℝ)', 'theorem exists_solS (a0 α : ℝ)')
body = rep(body, 'fun n => local_sol α _', 'fun n => local_solS a0 α _')
body = resub(body, r'/-- The flow of the clamped field from \(0, 0, α\)\. -/\nnoncomputable def flow \(α : ℝ\) : ℝ → ℝ × ℝ × ℝ := Classical\.choose \(exists_sol α\)',
           '/-- The flow of the clamped field from (a0, 0, α). -/\nnoncomputable def flowS (a0 α : ℝ) : ℝ → ℝ × ℝ × ℝ := Classical.choose (exists_solS a0 α)')
body = rep(body, 'theorem flow_zero (α : ℝ) : flow α 0 = (0, 0, α) := (Classical.choose_spec (exists_sol α)).1',
           'theorem flowS_zero (a0 α : ℝ) : flowS a0 α 0 = (a0, 0, α) := (Classical.choose_spec (exists_solS a0 α)).1')
body = rep(body, 'theorem flow_deriv (α : ℝ) :\n    ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (flow α) (vH t (flow α t)) (Ici 0) t :=\n  (Classical.choose_spec (exists_sol α)).2',
           'theorem flowS_deriv (a0 α : ℝ) :\n    ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (flowS a0 α) (vH t (flowS a0 α t)) (Ici 0) t :=\n  (Classical.choose_spec (exists_solS a0 α)).2')
k = body.index('/-- Continuity of the flow in α')
head, tail = body[:k], body[k:]
tail = rep(tail, 'theorem flow_cont (T : ℝ)', 'theorem flowS_cont (a0 : ℝ) (T : ℝ)')
tail = re.sub(r'\bflow (α₀|α|β)\b', r'flowS a0 \1', tail)
tail = rep(tail, '(flow_deriv β s hs.1)', '(flowS_deriv a0 β s hs.1)', 2)
tail = rep(tail, 'rw [flow_zero, flow_zero]', 'rw [flowS_zero, flowS_zero]')
assert re.search(r'\bflow(_\w+)?\b', tail.split('\n', 1)[1]) is None
out = HDR + f"import {NS}.{P}Flow\n/-! Scratch (run 2026-11-11T2228Z): the clamped {NAME} flow from (a0, 0, α), ported from\n`{D}/{P}Flow.lean` by `runs/2026-11-11T2228Z/scripts/port_suction_all.py`. -/\n\nnamespace Work.Suction.{T}Flow\nopen Set {NS}.{P}Base {NS}.{P}Flow\n\n" + head + tail + f"end Work.Suction.{T}Flow\n"
open(R + f'Work/Suction/{T}Flow.lean', 'w').write(out)
# ---- Limit
src = open(R + f'{D}/{P}Limit.lean').read()
a = src.index('theorem no_event')
e = src.index(f'end {NS}.{P}Limit')
body = src[a:e]
body = rep(body, 'theorem no_event {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (Y : ℝ → ℝ × ℝ × ℝ) (h0 : Y 0 = (0, 0, α))',
           'theorem no_eventS {a0 α : ℝ} (ha0 : 0 ≤ a0) (ha2 : a0 ≤ 2) (hα0 : 0 < α) (hα2 : α < 2) (Y : ℝ → ℝ × ℝ × ℝ)\n    (h0 : Y 0 = (a0, 0, α))')
body = rep(body, '    Filter.Tendsto (fun s => (Y s).2.1) Filter.atTop (nhds 1) := by',
           '    Filter.Tendsto (fun s => (Y s).2.1) Filter.atTop (nhds 1) ∧\n    (∀ t, 0 ≤ t → 0 ≤ (Y t).2.1 ∧ (Y t).2.1 < 1 ∧ 0 < (Y t).2.2) := by')
body = rep(body, 'have f0 : (Y 0).1 = 0 := by rw [h0]', 'have f0 : (Y 0).1 = a0 := by rw [h0]')
body = rep(body, """    have h1 : (Y 0).1 ≤ (Y t).1 := fmono (mem_Ici.2 le_rfl) ht ht
    rw [f0] at h1; exact h1""", """    have h1 : (Y 0).1 ≤ (Y t).1 := fmono (mem_Ici.2 le_rfl) ht ht
    rw [f0] at h1; linarith""")
body = rep(body, 'have fle : ∀ t, 0 ≤ t → (Y t).1 ≤ t := by', 'have fle : ∀ t, 0 ≤ t → (Y t).1 ≤ t + a0 := by')
body = rep(body, 'by linarith [fle t ht, le_max_left t 0]⟩)', 'by linarith [fle t ht, le_max_left t 0, ha2]⟩)')
body = resub(body, r"(    fun t ht => \(hq' t ht\)\.congr_deriv \(by rw \[[^\]]*\]\)), \?_⟩",
           r"\1, ?_,\n    fun t ht => ⟨pnn t ht, (key t ht).1, (key t ht).2⟩⟩")
out = HDR + f"import {NS}.{P}Limit\n/-! Scratch (run 2026-11-11T2228Z): `no_event` of `{D}/{P}Limit.lean` for a wall value\n0 ≤ f(0) = a0 ≤ 2, also exporting 0 ≤ p < 1 and q > 0; ported by `runs/2026-11-11T2228Z/scripts/port_suction_all.py`. -/\n\nnamespace Work.Suction.{T}Limit\nopen Set Filter Topology {NS}.{P}Base {NS}.{P}Limit\n\n" + body + f"end Work.Suction.{T}Limit\n"
open(R + f'Work/Suction/{T}Limit.lean', 'w').write(out)
# ---- Assemble
src = open(R + f'{D}/{P}Assemble.lean').read()
a = src.index('theorem cont_comp')
e = src.index(f'end {NS}.{P}Assemble')
body = src[a:e]
m = re.search(r'set lo : ℝ := ([0-9.]+) with hlo\n  set hi : ℝ := ([0-9.]+) with hhi', body)
olo, ohi = m.group(1), m.group(2)
body = re.sub(r'\bflow_zero\b', f'flowS_zero {A0}', body)
body = re.sub(r'\bflow_deriv\b', f'flowS_deriv {A0}', body)
body = re.sub(r'\bflow_cont\b', f'flowS_cont {A0}', body)
body = re.sub(r'\bflow\b', f'(flowS {A0})', body)
body = resub(body, r'theorem deriv_Icc \(α : ℝ\) : ∀ t ∈ Icc \(0 : ℝ\) [^,\n]+,\n    HasDerivWithinAt \(\(flowS [0-9.]+\) α\) \(vH t \(\(flowS [0-9.]+\) α t\)\) \(Icc 0 [^)\n]+(\))?\) t :=',
             f'theorem deriv_Icc (α : ℝ) : ∀ t ∈ Icc (0 : ℝ) ({L} : ℝ),\n    HasDerivWithinAt ((flowS {A0}) α) (vH t ((flowS {A0}) α t)) (Icc 0 ({L} : ℝ)) t :=')
body = rep(body, f'theorem under_lo : Under ((flowS {A0}) {olo}) :=\n  {NS}.{P[:-2]}UDataC.chainC',
           f'theorem under_lo : Under ((flowS {A0}) {LO}) :=\n  Work.Suction.{T}UData.chainC')
body = rep(body, f'theorem over_hi : Over ((flowS {A0}) {ohi}) :=\n  {NS}.{P[:-2]}ODataC.chainC',
           f'theorem over_hi : Over ((flowS {A0}) {HI}) :=\n  Work.Suction.{T}OData.chainC')
body = resub(body, r'/-- The [^\n]*boundary-value problem has a solution with wall shear strictly between\n[^\n]*-/\ntheorem exists_bvp :',
             f'/-- The {NAME} boundary-value problem with suction f(0) = {A0} has a solution with 0 ≤ p < 1,\nq > 0 and wall shear strictly between {LO} and {HI}. -/\ntheorem exists_bvpS :')
body = rep(body, f"""    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
    {olo} < q 0 ∧ q 0 < {ohi} := by
  set lo : ℝ := {olo} with hlo
  set hi : ℝ := {ohi} with hhi""", f"""    f 0 = {A0} ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
    {LO} < q 0 ∧ q 0 < {HI} ∧ (∀ t, 0 ≤ t → 0 ≤ p t ∧ p t < 1 ∧ 0 < q t) := by
  set lo : ℝ := {LO} with hlo
  set hi : ℝ := {HI} with hhi""")
body = resub(body, r'obtain ⟨d1, d2, d3, hlim⟩ := [\w.]+\.no_event ha0 ha2 \(\(flowS [0-9.]+\) a\) \(flowS_zero [0-9.]+ a\)\n    \(flowS_deriv [0-9.]+ a\) hback hnU hnO',
             f'obtain ⟨d1, d2, d3, hlim, hcl⟩ := Work.Suction.{T}Limit.no_eventS (by norm_num) (by norm_num) ha0 ha2\n    ((flowS {A0}) a) (flowS_zero {A0} a) (flowS_deriv {A0} a) hback hnU hnO')
body = rep(body, "d1, d2, d3, ?_, ?_, hlim, ?_, ?_⟩", "d1, d2, d3, ?_, ?_, hlim, ?_, ?_, ?_⟩")
body = rep(body, "    rw [hq0]; exact ha_lt\n", "    rw [hq0]; exact ha_lt\n  · exact hcl\n")
out = HDR + f"""import {NS}.{P}Base
import {NS}.{P}Flow
import Work.Suction.{T}Flow
import Work.Suction.{T}Limit
import Work.Suction.{T}UData
import Work.Suction.{T}OData
/-! Scratch (run 2026-11-11T2228Z): the supremum argument of `{D}/{P}Assemble.lean` for the
wall value f(0) = {A0} (suction), between the certified shooting values {LO} (undershoot) and {HI}
(overshoot); ported by `runs/2026-11-11T2228Z/scripts/port_suction_all.py`. -/

namespace Work.Suction.{T}Assemble
open Set Filter Topology {NS}.{P}Base {NS}.{P}Flow Work.Suction.{T}Flow

""" + body + f"end Work.Suction.{T}Assemble\n"
open(R + f'Work/Suction/{T}Assemble.lean', 'w').write(out)
print('ok', st, T)
