#!/usr/bin/env python3
"""Run 2026-11-11T2228Z: port the Hiemenz shooting stack (Checked/Hiemenz/HExFlow.lean, HExLimit.lean,
HExAssemble.lean) to a free wall value f(0) = a0 (suction), by exact replacements, each asserted.
Writes Work/Suction/HSFlow.lean, HSLimit.lean (local scratch modules; copied to runs/ for the record)."""
import re, sys
R = '/home/claude/formalization/'
def rep(s, old, new, n=None):
    c = s.count(old)
    assert c > 0 and (n is None or c == n), (old, c)
    return s.replace(old, new)

HDR = """import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
"""
# ---- HSFlow
src = open(R + 'Checked/Hiemenz/HExFlow.lean').read()
a = src.index('/-- A solution on [0, T] for every T > 0. -/')
b = src.index('/-- Forward uniqueness on [0, T]. -/')
c = src.index('theorem exists_sol (α : ℝ)')
e = src.index('end Checked.Hiemenz.HExFlow')
body = src[a:b] + src[c:e]
body = rep(body, 'theorem local_sol (α T : ℝ)', 'theorem local_solS (a0 α T : ℝ)', 1)
body = rep(body, 'Y 0 = (0, 0, α)', 'Y 0 = (a0, 0, α)', 3)
body = rep(body, '((0 : ℝ), (0 : ℝ), α)', '(a0, (0 : ℝ), α)', 1)
body = rep(body, 'theorem exists_sol (α : ℝ)', 'theorem exists_solS (a0 α : ℝ)', 1)
body = rep(body, 'fun n => local_sol α _', 'fun n => local_solS a0 α _', 1)
body = rep(body, '/-- The flow of the clamped field from (0, 0, α). -/\nnoncomputable def flow (α : ℝ) : ℝ → ℝ × ℝ × ℝ := Classical.choose (exists_sol α)',
           '/-- The flow of the clamped field from (a0, 0, α). -/\nnoncomputable def flowS (a0 α : ℝ) : ℝ → ℝ × ℝ × ℝ := Classical.choose (exists_solS a0 α)', 1)
body = rep(body, 'theorem flow_zero (α : ℝ) : flow α 0 = (0, 0, α) := (Classical.choose_spec (exists_sol α)).1',
           'theorem flowS_zero (a0 α : ℝ) : flowS a0 α 0 = (a0, 0, α) := (Classical.choose_spec (exists_solS a0 α)).1', 1)
body = rep(body, 'theorem flow_deriv (α : ℝ) :\n    ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (flow α) (vH t (flow α t)) (Ici 0) t :=\n  (Classical.choose_spec (exists_sol α)).2',
           'theorem flowS_deriv (a0 α : ℝ) :\n    ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (flowS a0 α) (vH t (flowS a0 α t)) (Ici 0) t :=\n  (Classical.choose_spec (exists_solS a0 α)).2', 1)
k = body.index('/-- Continuity of the flow in α')
head, tail = body[:k], body[k:]
tail = rep(tail, 'theorem flow_cont (T : ℝ)', 'theorem flowS_cont (a0 : ℝ) (T : ℝ)', 1)
tail = re.sub(r'\bflow (α₀|α|β)\b', r'flowS a0 \1', tail)
tail = rep(tail, '(flow_deriv β s hs.1)', '(flowS_deriv a0 β s hs.1)', 2)
tail = rep(tail, 'rw [flow_zero, flow_zero]', 'rw [flowS_zero, flowS_zero]', 1)
assert 'flow_' not in tail.replace('flowS_', ''), tail
assert re.search(r'\bflow\b', tail.split('\n', 1)[1]) is None
out = HDR + "import Checked.Hiemenz.HExFlow\n/-! Scratch (run 2026-11-11T2228Z): the clamped Hiemenz flow from (a0, 0, α), ported from\n`Checked/Hiemenz/HExFlow.lean` by `runs/2026-11-11T2228Z/scripts/port_suction.py`. -/\n\nnamespace Work.Suction.HSFlow\nopen Set Checked.Hiemenz.HExBase Checked.Hiemenz.HExFlow\n\n" + head + tail + "end Work.Suction.HSFlow\n"
open(R + 'Work/Suction/HSFlow.lean', 'w').write(out)

# ---- HSLimit
src = open(R + 'Checked/Hiemenz/HExLimit.lean').read()
a = src.index('theorem no_event')
e = src.index('end Checked.Hiemenz.HExLimit')
body = src[a:e]
body = rep(body, 'theorem no_event {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (Y : ℝ → ℝ × ℝ × ℝ) (h0 : Y 0 = (0, 0, α))',
           'theorem no_eventS {a0 α : ℝ} (ha0 : 0 ≤ a0) (ha2 : a0 ≤ 2) (hα0 : 0 < α) (hα2 : α < 2) (Y : ℝ → ℝ × ℝ × ℝ)\n    (h0 : Y 0 = (a0, 0, α))', 1)
body = rep(body, '    Filter.Tendsto (fun s => (Y s).2.1) Filter.atTop (nhds 1) := by',
           '    Filter.Tendsto (fun s => (Y s).2.1) Filter.atTop (nhds 1) ∧\n    (∀ t, 0 ≤ t → 0 ≤ (Y t).2.1 ∧ (Y t).2.1 < 1 ∧ 0 < (Y t).2.2) := by', 1)
body = rep(body, 'have f0 : (Y 0).1 = 0 := by rw [h0]', 'have f0 : (Y 0).1 = a0 := by rw [h0]', 1)
body = rep(body, """    have h1 : (Y 0).1 ≤ (Y t).1 := fmono (mem_Ici.2 le_rfl) ht ht
    rw [f0] at h1; exact h1""", """    have h1 : (Y 0).1 ≤ (Y t).1 := fmono (mem_Ici.2 le_rfl) ht ht
    rw [f0] at h1; linarith""", 1)
body = rep(body, 'have fle : ∀ t, 0 ≤ t → (Y t).1 ≤ t := by', 'have fle : ∀ t, 0 ≤ t → (Y t).1 ≤ t + a0 := by', 1)
body = rep(body, 'by linarith [fle t ht, le_max_left t 0]⟩)', 'by linarith [fle t ht, le_max_left t 0, ha2]⟩)', 1)
body = rep(body, """    fun t ht => (hq' t ht).congr_deriv (by rw [clf t ht, clq t ht, clp t ht]), ?_⟩""",
           """    fun t ht => (hq' t ht).congr_deriv (by rw [clf t ht, clq t ht, clp t ht]), ?_,
    fun t ht => ⟨pnn t ht, (key t ht).1, (key t ht).2⟩⟩""", 1)
out = HDR + "import Checked.Hiemenz.HExLimit\n/-! Scratch (run 2026-11-11T2228Z): `no_event` of `Checked/Hiemenz/HExLimit.lean` for a wall value\n0 ≤ f(0) = a0 ≤ 2, also exporting 0 ≤ p < 1 and q > 0; ported by `runs/2026-11-11T2228Z/scripts/port_suction.py`. -/\n\nnamespace Work.Suction.HSLimit\nopen Set Filter Topology Checked.Hiemenz.HExBase Checked.Hiemenz.HExLimit\n\n" + body + "end Work.Suction.HSLimit\n"
open(R + 'Work/Suction/HSLimit.lean', 'w').write(out)
print('ok')

# ---- HSAssemble (wall value 0.5, window (1.5, 1.6), chains on [0, 2])
src = open(R + 'Checked/Hiemenz/HExAssemble.lean').read()
a = src.index('theorem cont_comp')
e = src.index('end Checked.Hiemenz.HExAssemble')
body = src[a:e]
body = re.sub(r'\bflow_zero\b', 'flowS_zero 0.5', body)
body = re.sub(r'\bflow_deriv\b', 'flowS_deriv 0.5', body)
body = re.sub(r'\bflow_cont\b', 'flowS_cont 0.5', body)
body = re.sub(r'\bflow\b', '(flowS 0.5)', body)
body = rep(body, """theorem deriv_Icc (α : ℝ) : ∀ t ∈ Icc (0 : ℝ) (15 / 2),
    HasDerivWithinAt ((flowS 0.5) α) (vH t ((flowS 0.5) α t)) (Icc 0 (15 / 2)) t :=""",
"""theorem deriv_Icc (α : ℝ) : ∀ t ∈ Icc (0 : ℝ) (2 / 1),
    HasDerivWithinAt ((flowS 0.5) α) (vH t ((flowS 0.5) α t)) (Icc 0 (2 / 1)) t :=""", 1)
body = rep(body, """theorem under_lo : Under ((flowS 0.5) 1.2325876568) :=
  Checked.Hiemenz.HUDataC.chainC (deriv_Icc _) (flowS_zero 0.5 _)""",
"""theorem under_lo : Under ((flowS 0.5) 1.5) :=
  Work.Suction.HSUData.chainC (deriv_Icc _) (flowS_zero 0.5 _)""", 1)
body = rep(body, """theorem over_hi : Over ((flowS 0.5) 1.2325876569) :=
  Checked.Hiemenz.HODataC.chainC (deriv_Icc _) (flowS_zero 0.5 _)""",
"""theorem over_hi : Over ((flowS 0.5) 1.6) :=
  Work.Suction.HSOData.chainC (deriv_Icc _) (flowS_zero 0.5 _)""", 1)
body = rep(body, """/-- The Hiemenz boundary-value problem has a solution with wall shear strictly between
1.2325876568 and 1.2325876569. -/
theorem exists_bvp : ∃ f p q : ℝ → ℝ,""", """/-- The Hiemenz boundary-value problem with suction f(0) = 1/2 has a solution with 0 ≤ p < 1,
q > 0 and wall shear strictly between 1.5 and 1.6. -/
theorem exists_bvpS : ∃ f p q : ℝ → ℝ,""", 1)
body = rep(body, """    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
    1.2325876568 < q 0 ∧ q 0 < 1.2325876569 := by
  set lo : ℝ := 1.2325876568 with hlo
  set hi : ℝ := 1.2325876569 with hhi""", """    f 0 = 0.5 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
    1.5 < q 0 ∧ q 0 < 1.6 ∧ (∀ t, 0 ≤ t → 0 ≤ p t ∧ p t < 1 ∧ 0 < q t) := by
  set lo : ℝ := 1.5 with hlo
  set hi : ℝ := 1.6 with hhi""", 1)
body = rep(body, """  obtain ⟨d1, d2, d3, hlim⟩ := Checked.Hiemenz.HExLimit.no_event ha0 ha2 ((flowS 0.5) a) (flowS_zero 0.5 a)
    (flowS_deriv 0.5 a) hback hnU hnO""", """  obtain ⟨d1, d2, d3, hlim, hcl⟩ := Work.Suction.HSLimit.no_eventS (by norm_num) (by norm_num) ha0 ha2
    ((flowS 0.5) a) (flowS_zero 0.5 a) (flowS_deriv 0.5 a) hback hnU hnO""", 1)
body = rep(body, "d1, d2, d3, ?_, ?_, hlim, ?_, ?_⟩", "d1, d2, d3, ?_, ?_, hlim, ?_, ?_, ?_⟩", 1)
body = rep(body, """    rw [hq0]; exact ha_lt
""", """    rw [hq0]; exact ha_lt
  · exact hcl
""", 1)
out = HDR + """import Checked.Hiemenz.HExBase
import Checked.Hiemenz.HExFlow
import Work.Suction.HSFlow
import Work.Suction.HSLimit
import Work.Suction.HSUData
import Work.Suction.HSOData
/-! Scratch (run 2026-11-11T2228Z): the supremum argument of `Checked/Hiemenz/HExAssemble.lean` for the
wall value f(0) = 1/2 (suction), between the certified shooting values 1.5 (undershoot) and 1.6
(overshoot); ported by `runs/2026-11-11T2228Z/scripts/port_suction.py`. -/

namespace Work.Suction.HSAssemble
open Set Filter Topology Checked.Hiemenz.HExBase Checked.Hiemenz.HExFlow Work.Suction.HSFlow

""" + body + "end Work.Suction.HSAssemble\n"
open(R + 'Work/Suction/HSAssemble.lean', 'w').write(out)
print('ok assemble')
