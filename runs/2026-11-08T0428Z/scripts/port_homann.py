"""Run 2026-11-08T0428Z: port the Hiemenz existence modules (Work/Hiemenz/HEx*.lean, HCellWC.lean) to
the Homann field q' = -2 g q - 1 + p^2 by text substitution (each replacement must match)."""
import re, sys
R = 'Work/Hiemenz/'; W = 'Work/Homann/'
names = {'HExBase': 'HmExBase', 'HExFlow': 'HmExFlow', 'HExLimit': 'HmExLimit', 'HExAssemble': 'HmExAssemble',
         'HCellWC': 'HmCellWC', 'HUDataC': 'HmUDataC', 'HODataC': 'HmODataC'}
def common(s):
    for a, b in names.items():
        s = s.replace('Work.Hiemenz.' + a, 'Work.Homann.' + b)
    s = s.replace('-(cl (max ', '-(2 * cl (max ')
    return s
def rep(s, a, b, cnt=1):
    n = s.count(a); assert n == cnt, (a, n); return s.replace(a, b)
out = {}
# HExBase
s = common(open(R + 'HExBase.lean').read())
s = rep(s, '# Hiemenz existence: the clamped field and the two shooting events (run 2026-11-07T2028Z)',
        '# Homann existence: the clamped field and the two shooting events (run 2026-11-08T0428Z)')
s = rep(s, "`vH t y` is the Hiemenz field (p, q, −f q − 1 + p²)", "`vH t y` is the Homann field (p, q, −2 f q − 1 + p²)")
s = rep(s, "(`Work.Hiemenz.hiemenz_under`, `hiemenz_over`)", "(`Work.Homann.homann_under`, `homann_over`); ported from `Work.Hiemenz.HExBase`")
s = rep(s, "/-- The clamped Hiemenz field. -/", "/-- The clamped Homann field. -/")
out['HmExBase'] = s
# HExFlow
s = common(open(R + 'HExFlow.lean').read())
s = rep(s, '# Hiemenz existence: a global flow of the clamped field (run 2026-11-07T2028Z)',
        '# Homann existence: a global flow of the clamped field (run 2026-11-08T0428Z, ported from `Work.Hiemenz.HExFlow`)')
s = rep(s, "`exists_sol`: the clamped Hiemenz field", "`exists_sol`: the clamped Homann field")
s = rep(s, "Real.toNNReal (T + 8)", "Real.toNNReal (2 * T + 12)", 4)
s = rep(s, "  rw [Real.coe_toNNReal _ (by linarith)]\n  simp only [vH,", "  rw [Real.coe_toNNReal _ (by linarith)]\n  simp only [vH,")
s = rep(s, """    have e : -(a * b) - 1 + c ^ 2 - (-(a' * b') - 1 + c' ^ 2)
        = -((a - a') * b + a' * (b - b')) + (c + c') * (c - c') := by ring""",
"""    have e : -(2 * a * b) - 1 + c ^ 2 - (-(2 * a' * b') - 1 + c' ^ 2)
        = -(2 * ((a - a') * b + a' * (b - b'))) + (c + c') * (c - c') := by ring""")
s = rep(s, """    have h5 := abs_add_le (-((a - a') * b + a' * (b - b'))) ((c + c') * (c - c'))
    rw [abs_neg] at h5""", """    have h5 := abs_add_le (-(2 * ((a - a') * b + a' * (b - b')))) ((c + c') * (c - c'))
    rw [abs_neg, abs_mul, abs_two] at h5""")
s = s.replace("2 * T + 9", "4 * T + 13")
s = rep(s, """  have hab : |cl C y.1 * cl 2 y.2.2| ≤ C * 2 := by
    rw [abs_mul]; exact mul_le_mul h3 h2 (abs_nonneg _) hC0""", """  have hab : |2 * cl C y.1 * cl 2 y.2.2| ≤ 2 * C * 2 := by
    rw [abs_mul, abs_mul, abs_two]; nlinarith [abs_nonneg (cl C y.1), abs_nonneg (cl 2 y.2.2)]""")
s = rep(s, """  have k1 := abs_add_le (-(cl C y.1 * cl 2 y.2.2) - 1) (cl 2 y.2.1 ^ 2)
  have k2 := abs_sub (-(cl C y.1 * cl 2 y.2.2)) 1""", """  have k1 := abs_add_le (-(2 * cl C y.1 * cl 2 y.2.2) - 1) (cl 2 y.2.1 ^ 2)
  have k2 := abs_sub (-(2 * cl C y.1 * cl 2 y.2.2)) 1""")
out['HmExFlow'] = s
# HExLimit
s = common(open(R + 'HExLimit.lean').read())
s = s.replace("Hiemenz", "Homann")
s = rep(s, "      (-((Y t).1 * (Y t).2.2) - 1 + (Y t).2.1 ^ 2) (Ici 0) t) ∧", "      (-(2 * (Y t).1 * (Y t).2.2) - 1 + (Y t).2.1 ^ 2) (Ici 0) t) ∧")
out['HmExLimit'] = s
# HExAssemble
s = common(open(R + 'HExAssemble.lean').read())
s = s.replace("1.2325876568", "1.3119376938").replace("1.2325876569", "1.3119376939")
s = s.replace("(15 / 2)", "6")
s = rep(s, "    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 + p η ^ 2) (Ici 0) η) ∧",
           "    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(2 * f η * q η) - 1 + p η ^ 2) (Ici 0) η) ∧")
s = s.replace("run 2026-11-07T2028Z", "run 2026-11-08T0428Z, ported from `Work.Hiemenz.HExAssemble`").replace("Hiemenz", "Homann")
out['HmExAssemble'] = s
# HCellWC
s = common(open(R + 'HCellWC.lean').read())
s = rep(s, "def defect3 (c : Cell) : List ℚ := qsub (qadd (qadd (qderiv c.pq) (qmul c.pg c.pq)) [1]) (qmul c.pp c.pp)",
        "def defect3 (c : Cell) : List ℚ :=\n  qsub (qadd (qadd (qderiv c.pq) (qmul (qadd c.pg c.pg) c.pq)) [1]) (qmul c.pp c.pp)")
s = rep(s, "/-- The third defect pq′ + pg·pq + 1 − pp². -/", "/-- The third defect pq′ + 2·pg·pq + 1 − pp². -/")
for a in ["(mlo c) (qlo c) (2 * plo c - c.r2)", "(mlo c) (qlo c) (2 * phi c + c.r2)",
          "(mlo c) (qhi c) (2 * plo c - c.r2)", "(mlo c) (qhi c) (2 * phi c + c.r2)"]:
    s = rep(s, a, a.replace("(mlo c)", "(2 * mlo c)").replace("(qlo c)", "(2 * qlo c)").replace("(qhi c)", "(2 * qhi c)"))
s = rep(s, "    dEvalQ c.pq σ + evalQ c.pg σ * evalQ c.pq σ + 1 - evalQ c.pp σ ^ 2 = evalQ (defect3 c) σ := by",
        "    dEvalQ c.pq σ + 2 * evalQ c.pg σ * evalQ c.pq σ + 1 - evalQ c.pp σ ^ 2 = evalQ (defect3 c) σ := by")
s = rep(s, "theorem os_hiemenz", "theorem os_homann")
s = rep(s, """    (hm : m ≤ y1) (hq1 : ql ≤ P3) (hq2 : P3 ≤ qh) (hs1 : sl ≤ y2 + P2) (hs2 : y2 + P2 ≤ sh) :
    w1 * (y2 - P2) * (y1 - P1) + w2 * (y3 - P3) * (y2 - P2)
      + ((-(y1 * y3) - 1 + y2 ^ 2) - (-(P1 * P3) - 1 + P2 ^ 2)) * (y3 - P3)""",
"""    (hm : m ≤ 2 * y1) (hq1 : ql ≤ 2 * P3) (hq2 : 2 * P3 ≤ qh) (hs1 : sl ≤ y2 + P2) (hs2 : y2 + P2 ≤ sh) :
    w1 * (y2 - P2) * (y1 - P1) + w2 * (y3 - P3) * (y2 - P2)
      + ((-(2 * y1 * y3) - 1 + y2 ^ 2) - (-(2 * P1 * P3) - 1 + P2 ^ 2)) * (y3 - P3)""")
s = rep(s, """      - (w1 * e2 * e1 + w2 * e3 * e2 + ((-(y1 * y3) - 1 + y2 ^ 2) - (-(P1 * P3) - 1 + P2 ^ 2)) * e3)
      = qf μ w1 w2 m P3 s e1 e2 e3 + (y1 - m) * e3 ^ 2 := by""",
"""      - (w1 * e2 * e1 + w2 * e3 * e2 + ((-(2 * y1 * y3) - 1 + y2 ^ 2) - (-(2 * P1 * P3) - 1 + P2 ^ 2)) * e3)
      = qf μ w1 w2 m (2 * P3) s e1 e2 e3 + (2 * y1 - m) * e3 ^ 2 := by""")
s = rep(s, "  have hy : 0 ≤ (y1 - m) * e3 ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)",
        "  have hy : 0 ≤ (2 * y1 - m) * e3 ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)")
s = rep(s, """  have hQ : 0 ≤ qf μ w1 w2 m P3 s e1 e2 e3 := by
    rcases le_total 0 (e1 * e3) with h | h
    · have := dP P3 ql s
      have : 0 ≤ (P3 - ql) * (e1 * e3) := mul_nonneg (by linarith) h
      linarith [hS ql H1 H2]
    · have := dP P3 qh s
      have : 0 ≤ (qh - P3) * (-(e1 * e3)) := mul_nonneg (by linarith) (by linarith)""",
"""  have hQ : 0 ≤ qf μ w1 w2 m (2 * P3) s e1 e2 e3 := by
    rcases le_total 0 (e1 * e3) with h | h
    · have := dP (2 * P3) ql s
      have : 0 ≤ (2 * P3 - ql) * (e1 * e3) := mul_nonneg (by linarith) h
      linarith [hS ql H1 H2]
    · have := dP (2 * P3) qh s
      have : 0 ≤ (qh - 2 * P3) * (-(e1 * e3)) := mul_nonneg (by linarith) (by linarith)""")
open('/tmp/claude-0/hcellwc_partial.lean', 'w').write(s)
out['HmCellWC'] = s
for k, v in out.items():
    open(W + k + '.lean', 'w').write(v)
print('ok')
