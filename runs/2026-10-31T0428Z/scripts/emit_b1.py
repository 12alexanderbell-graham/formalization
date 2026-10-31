"""Emit the numerical certificates for Work/Cosmography/B1Truncation.lean (run 2026-10-31T0428Z).

Lower bounds of J(Ω,w) = ∫_w^1 2/√(Ω+(1−Ω)v⁶) dv: right Riemann sum (the integrand decreases in v)
with the tangent bound 2/√y ≥ 3c − c³y (any c ≥ 0); c_i ≈ 1/√y_i at the midpoint Ω* of the Ω-piece.
Upper bounds: left Riemann sum with the secant bound 1/√y ≤ 1/p − (y−p²)/(pq(p+q)), p² ≤ y ≤ q²,
p_i ≤ √y(a, v_i), q_i ≥ √y(b, v_i) on the piece [a,b] (y increases in Ω for v ≤ 1).
Lean only checks: every c, p, q is a natural number / 10⁵; the sums are evaluated by norm_num.
This script also checks the final polynomial inequalities exactly (sympy), as a preview.
Run: python3 emit_b1.py > data.lean
"""
import math, sympy as sp
from fractions import Fraction as Fr
D = 10**5
L2HI = Fr(6931471808, 10**10); L2LO = Fr(6931471803, 10**10)
PIECES = [(Fr(1, 5), Fr(3, 10)), (Fr(3, 10), Fr(2, 5))]
def y(O, v): return O + (1 - O) * v**6
def lower(Os, w0, N):
    h = (1 - w0) / N; cs = []; A = Fr(0); B = Fr(0)
    for i in range(N):
        v = w0 + (i + 1) * h
        c = round(1 / math.sqrt(float(y(Os, v))) * D); cs.append(c); c = Fr(c, D)
        A += h * (3 * c - c**3 * v**6); B += h * c**3 * (1 - v**6)
    return cs, A, B          # sum = A - B Ω
def upper(a, b, w0, N):
    h = (1 - w0) / N; ps = []; qs = []; C = Fr(0); Dd = Fr(0)
    for i in range(N):
        v = w0 + i * h
        p = math.floor(math.sqrt(float(y(a, v))) * D); q = math.ceil(math.sqrt(float(y(b, v))) * D)
        while Fr(p, D)**2 > y(a, v): p -= 1
        while Fr(q, D)**2 < y(b, v): q += 1
        ps.append(p); qs.append(q); P = Fr(p, D); Q = Fr(q, D); K = P * Q * (P + Q)
        C += h * 2 * (1 / P - (v**6 - P**2) / K); Dd += -h * 2 * (1 - v**6) / K
    return ps, qs, C, Dd     # sum = C + D Ω
def down(x, k=8): return Fr(math.floor(x * 10**k), 10**k)
def up(x, k=8): return Fr(math.ceil(x * 10**k), 10**k)
def lean_list(name, xs): return f"def {name} : List ℕ := [{', '.join(map(str, xs))}]"
def q(x): return f"({x.numerator}/{x.denominator} : ℝ)"
O = sp.symbols('O')
def Qp(u): return u + (Fr(3, 2) - Fr(3, 4) * O) * u**2 + (Fr(9, 8) * O**2 - 2 * O + Fr(7, 6)) * u**3
def kap(c): return c / 5 * Fr(10, 3) * L2HI
def minon(f, a, b):
    xs = [a, b] + [r for r in sp.solve(sp.diff(f, O), O) if r.is_real and a <= r <= b]
    return min(f.subs(O, x) for x in xs)
out = []; checks = []
W3, W7 = Fr(1, 2), Fr(3536, 10000)
low = {}
for tag, w0 in (("Z3", W3), ("Z7", W7)):
    for k, (a, b) in enumerate(PIECES):
        cs, A, B = lower((a + b) / 2, w0, 40)
        Ad, Bu = down(A), up(B); low[(tag, k)] = (Ad, Bu)
        out.append(lean_list(f"c{tag}{k}", cs))
        out.append(f"-- c{tag}{k}: sum = A - B Ω with A ≈ {float(A):.10f}, B ≈ {float(B):.10f}; used A' = {Ad}, B' = {Bu}")
upp = {}
for k, (a, b) in enumerate(PIECES):
    ps, qs, C, Dd = upper(a, b, W3, 80)
    Cu, Du = up(C), up(Dd); upp[k] = (Cu, Du)
    out.append(lean_list(f"pZ3{k}", ps)); out.append(lean_list(f"qZ3{k}", qs))
    out.append(f"-- pZ3{k}/qZ3{k}: sum = C + D Ω with C ≈ {float(C):.10f}, D ≈ {float(Dd):.10f}; used C' = {Cu}, D' = {Du}")
for k, (a, b) in enumerate(PIECES):
    A3, B3 = low[("Z3", k)]; A7, B7 = low[("Z7", k)]; C3, D3 = upp[k]
    m3 = minon(sp.expand(4 * (A3 - B3 * O) * (1 - kap(Fr(9, 100))) - Qp(2 * L2HI)), a, b)
    m7 = minon(sp.expand(8 * (A7 - B7 * O) * (1 - kap(Fr(3, 10))) - Qp(3 * L2HI)), a, b)
    ms = minon(sp.expand(2 * (A7 - B7 * O) * Qp(2 * L2LO) * (1 - kap(Fr(18, 100))) - (C3 + D3 * O) * Qp(3 * L2HI)), a, b)
    checks.append(f"-- piece {k} [{a},{b}]: margins z3 {float(m3):.5f}, z7 {float(m7):.5f}, shape {float(ms):.5f}")
print("\n".join(out)); print("\n".join(checks))

# ---- Lean lemmas (printed after the data; the main file includes them verbatim) ----
def leanR(x): return f"({x.numerator} / {x.denominator} : ℝ)" if x.denominator != 1 else f"({x.numerator} : ℝ)"
lem = []
for tag, w0, wl in (("Z3", W3, "(1/2:ℝ)"), ("Z7", W7, "(3536/10000:ℝ)")):
    hden = (1 - w0) / 40
    for k, (a, b) in enumerate(PIECES):
        A, B = low[(tag, k)]
        lem.append(f"""
lemma J{tag[1]}_lower{k} (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1) :
    {leanR(A)} - {leanR(B)} * Ω ≤ ∫ v in {wl}..1, gL Ω v := by
  have key := J_lower Ω hΩ₀ hΩ₁ {wl} {leanR(hden)} (by norm_num) (by norm_num) 40
    (fun i => (c{tag}{k}.getD i 0 : ℝ) / 100000) (fun i => by positivity)
  have e : {wl} + ((40:ℕ):ℝ) * {leanR(hden)} = 1 := by norm_num
  rw [e] at key
  refine le_trans ?_ key
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, c{tag}{k}]
  norm_num
  linarith""")
for k, (a, b) in enumerate(PIECES):
    C, Dd = upp[k]
    lem.append(f"""
set_option maxHeartbeats 8000000 in
lemma J3_upper{k} (Ω : ℝ) (hΩa : {leanR(a)} ≤ Ω) (hΩb : Ω ≤ {leanR(b)}) :
    ∫ v in (1/2:ℝ)..1, gL Ω v ≤ {leanR(C)} + {leanR(Dd)} * Ω := by
  have hp1 : ∀ i : ℕ, i < 80 → ((pZ3{k}.getD i 0 : ℝ) / 100000) ^ 2 ≤
      {leanR(a)} + (1 - {leanR(a)}) * (1/2 + (i:ℝ) * (1/160)) ^ 6 := by
    intro i hi; interval_cases i <;> norm_num [pZ3{k}]
  have hq1 : ∀ i : ℕ, i < 80 → {leanR(b)} + (1 - {leanR(b)}) * (1/2 + (i:ℝ) * (1/160)) ^ 6 ≤
      ((qZ3{k}.getD i 0 : ℝ) / 100000) ^ 2 := by
    intro i hi; interval_cases i <;> norm_num [qZ3{k}]
  have hpp : ∀ i : ℕ, i < 80 → (0:ℝ) < (pZ3{k}.getD i 0 : ℝ) / 100000 := by
    intro i hi; interval_cases i <;> norm_num [pZ3{k}]
  have hqp : ∀ i : ℕ, i < 80 → (0:ℝ) < (qZ3{k}.getD i 0 : ℝ) / 100000 := by
    intro i hi; interval_cases i <;> norm_num [qZ3{k}]
  have hv : ∀ i : ℕ, i < 80 → (0:ℝ) ≤ 1/2 + (i:ℝ) * (1/160) ∧ 1/2 + (i:ℝ) * (1/160) ≤ 1 := by
    intro i hi
    have : (i:ℝ) ≤ 79 := by exact_mod_cast Nat.le_of_lt_succ hi
    constructor <;> nlinarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)]
  have key := J_upper Ω (by linarith) (by linarith) (1/2) (1/160) (by norm_num) (by norm_num) 80
    (fun i => (pZ3{k}.getD i 0 : ℝ) / 100000) (fun i => (qZ3{k}.getD i 0 : ℝ) / 100000) hpp hqp
    (fun i hi => le_trans (hp1 i hi) (y_mono Ω _ _ hΩa (hv i hi).1 (hv i hi).2))
    (fun i hi => le_trans (y_mono _ Ω _ hΩb (hv i hi).1 (hv i hi).2) (hq1 i hi))
  have e : (1/2:ℝ) + ((80:ℕ):ℝ) * (1/160) = 1 := by norm_num
  rw [e] at key
  refine le_trans key ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pZ3{k}, qZ3{k}]
  norm_num
  linarith""")
open('lemmas.lean.txt', 'w').write("\n".join(lem) + "\n")
