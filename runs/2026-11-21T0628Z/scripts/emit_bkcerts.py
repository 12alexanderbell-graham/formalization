"""Emit Checked/Trust/NecessityBKCerts.lean (run 2026-11-21T0628Z): enclosures of the B1 distance integrals
J3 = ∫_{1/2}^1 gL and J7 = ∫_{√(1/8)}^1 gL for densities 0 ≤ Ω ≤ 1/5, by the method and the Lean lemmas of
Checked/Cosmography/B1Truncation.lean (generator runs/2026-10-31T0428Z/scripts/emit_b1.py, here with five
Ω-pieces), plus the polynomial inequality of each piece. Lean checks every number.
Run from the repository root: python3 runs/2026-11-21T0628Z/scripts/emit_bkcerts.py > Checked/Trust/NecessityBKCerts.lean
"""
import math, sympy as sp
from fractions import Fraction as Fr
D = 10**5
L2HI = Fr(6931471808, 10**10); L2LO = Fr(6931471803, 10**10)
PIECES = [(Fr(0), Fr(1, 50)), (Fr(1, 50), Fr(1, 20)), (Fr(1, 20), Fr(1, 10)), (Fr(1, 10), Fr(3, 20)), (Fr(3, 20), Fr(1, 5))]
def y(O, v): return O + (1 - O) * v**6
def lower(Os, w0, N):
    h = (1 - w0) / N; cs = []; A = Fr(0); B = Fr(0)
    for i in range(N):
        v = w0 + (i + 1) * h
        c = round(1 / math.sqrt(float(y(Os, v))) * D); cs.append(c); c = Fr(c, D)
        A += h * (3 * c - c**3 * v**6); B += h * c**3 * (1 - v**6)
    return cs, A, B
def upper(a, b, w0, N):
    h = (1 - w0) / N; ps = []; qs = []; C = Fr(0); Dd = Fr(0)
    for i in range(N):
        v = w0 + i * h
        p = math.floor(math.sqrt(float(y(a, v))) * D); q = math.ceil(math.sqrt(float(y(b, v))) * D)
        while Fr(p, D)**2 > y(a, v): p -= 1
        while Fr(q, D)**2 < y(b, v): q += 1
        ps.append(p); qs.append(q); P = Fr(p, D); Q = Fr(q, D); K = P * Q * (P + Q)
        C += h * 2 * (1 / P - (v**6 - P**2) / K); Dd += -h * 2 * (1 - v**6) / K
    return ps, qs, C, Dd
def down(x, k=8): return Fr(math.floor(x * 10**k), 10**k)
def up(x, k=8): return Fr(math.ceil(x * 10**k), 10**k)
def R(x): return f"({x.numerator} / {x.denominator} : ℝ)" if x.denominator != 1 else f"({x.numerator} : ℝ)"
O = sp.symbols('O')
def Qp(u): return u + (Fr(3, 2) - Fr(3, 4) * O) * u**2 + (Fr(9, 8) * O**2 - 2 * O + Fr(7, 6)) * u**3
def kap(c): return c / 5 * Fr(10, 3) * L2HI
def minon(f, a, b):
    xs = [a, b] + [r for r in sp.solve(sp.diff(f, O), O) if r.is_real and a <= r <= b]
    return min(f.subs(O, x) for x in xs)
W3, W7 = Fr(1, 2), Fr(3536, 10000)
low = {}; upp = {}; data = []; lem = []; checks = []
for tag, w0 in (("3", W3), ("7", W7)):
    for k, (a, b) in enumerate(PIECES):
        cs, A, B = lower((a + b) / 2, w0, 40)
        low[(tag, k)] = (down(A), up(B))
        data.append(f"def bkc{tag}{k} : List ℕ := [{', '.join(map(str, cs))}]")
for k, (a, b) in enumerate(PIECES):
    ps, qs, C, Dd = upper(a, b, W3, 80)
    upp[k] = (up(C), up(Dd))
    data.append(f"def bkp{k} : List ℕ := [{', '.join(map(str, ps))}]")
    data.append(f"def bkq{k} : List ℕ := [{', '.join(map(str, qs))}]")
for k, (a, b) in enumerate(PIECES):
    A3, B3 = low[("3", k)]; A7, B7 = low[("7", k)]; C3, D3 = upp[k]
    m3 = minon(sp.expand(4 * (A3 - B3 * O) * (1 - kap(Fr(9, 100))) - Qp(2 * L2HI)), a, b)
    m7 = minon(sp.expand(8 * (A7 - B7 * O) * (1 - kap(Fr(3, 10))) - Qp(3 * L2HI)), a, b)
    ms = minon(sp.expand(8 * (A7 - B7 * O) * Qp(2 * L2LO) * (1 - kap(Fr(18, 100))) - 4 * (C3 + D3 * O) * Qp(3 * L2HI)), a, b)
    assert m3 > 0 and m7 > 0 and ms > 0, (k, m3, m7, ms)
    checks.append(f"-- piece {k} [{a}, {b}]: margins z3 {float(m3):.5f}, z7 {float(m7):.5f}, shape {float(ms):.5f}")
for k, (a, b) in enumerate(PIECES):
    for tag, w0, wl in (("3", W3, "(1/2:ℝ)"), ("7", W7, "(3536/10000:ℝ)")):
        A, B = low[(tag, k)]; hden = (1 - w0) / 40
        body = f"""
theorem bkJ{tag}_lo{k}' (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1) :
    {R(A)} - {R(B)} * Ω ≤ ∫ v in {wl}..1, gL Ω v := by
  have key := J_lower Ω hΩ₀ hΩ₁ {wl} {R(hden)} (by norm_num) (by norm_num) 40
    (fun i => (bkc{tag}{k}.getD i 0 : ℝ) / 100000) (fun i => by positivity)
  have e : {wl} + ((40:ℕ):ℝ) * {R(hden)} = 1 := by norm_num
  rw [e] at key
  refine le_trans ?_ key
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bkc{tag}{k}]
  norm_num
  linarith"""
        lem.append(body)
    A7, B7 = low[("7", k)]
    lem.append(f"""
theorem bkJ7_lo{k} (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1) :
    {R(A7)} - {R(B7)} * Ω ≤ ∫ v in √(1 / (1 + 7) : ℝ)..1, gL Ω v := by
  have hs0 : 0 < √(1 / (1 + 7) : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hs : √(1 / (1 + 7) : ℝ) ≤ 3536 / 10000 := by
    rw [show (3536 / 10000 : ℝ) = √((3536 / 10000) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  exact le_trans (bkJ7_lo{k}' Ω hΩ₀ hΩ₁) (J_shift Ω hΩ₀ hΩ₁ _ _ hs0 hs (by norm_num))""")
    C, Dd = upp[k]
    lem.append(f"""
set_option maxHeartbeats 8000000 in
theorem bkJ3_up{k} (Ω : ℝ) (hΩa : {R(a)} ≤ Ω) (hΩb : Ω ≤ {R(b)}) :
    ∫ v in (1/2:ℝ)..1, gL Ω v ≤ {R(C)} + {R(Dd)} * Ω := by
  have hp1 : ∀ i : ℕ, i < 80 → ((bkp{k}.getD i 0 : ℝ) / 100000) ^ 2 ≤
      {R(a)} + (1 - {R(a)}) * (1/2 + (i:ℝ) * (1/160)) ^ 6 := by
    intro i hi; interval_cases i <;> norm_num [bkp{k}]
  have hq1 : ∀ i : ℕ, i < 80 → {R(b)} + (1 - {R(b)}) * (1/2 + (i:ℝ) * (1/160)) ^ 6 ≤
      ((bkq{k}.getD i 0 : ℝ) / 100000) ^ 2 := by
    intro i hi; interval_cases i <;> norm_num [bkq{k}]
  have hpp : ∀ i : ℕ, i < 80 → (0:ℝ) < (bkp{k}.getD i 0 : ℝ) / 100000 := by
    intro i hi; interval_cases i <;> norm_num [bkp{k}]
  have hqp : ∀ i : ℕ, i < 80 → (0:ℝ) < (bkq{k}.getD i 0 : ℝ) / 100000 := by
    intro i hi; interval_cases i <;> norm_num [bkq{k}]
  have hv : ∀ i : ℕ, i < 80 → (0:ℝ) ≤ 1/2 + (i:ℝ) * (1/160) ∧ 1/2 + (i:ℝ) * (1/160) ≤ 1 := by
    intro i hi
    have : (i:ℝ) ≤ 79 := by exact_mod_cast Nat.le_of_lt_succ hi
    constructor <;> nlinarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)]
  have key := J_upper Ω (by linarith) (by linarith) (1/2) (1/160) (by norm_num) (by norm_num) 80
    (fun i => (bkp{k}.getD i 0 : ℝ) / 100000) (fun i => (bkq{k}.getD i 0 : ℝ) / 100000) hpp hqp
    (fun i hi => le_trans (hp1 i hi) (y_mono Ω _ _ hΩa (hv i hi).1 (hv i hi).2))
    (fun i hi => le_trans (y_mono _ Ω _ hΩb (hv i hi).1 (hv i hi).2) (hq1 i hi))
  have e : (1/2:ℝ) + ((80:ℕ):ℝ) * (1/160) = 1 := by norm_num
  rw [e] at key
  refine le_trans key ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bkp{k}, bkq{k}]
  norm_num
  linarith""")
    A3, B3 = low[("3", k)]
    lem.append(f"""
theorem bkz3_poly{k} (Ω : ℝ) (ha : {R(a)} ≤ Ω) (hb : Ω ≤ {R(b)}) :
    Qc Ω (2 * 0.6931471808) < 4 * ({R(A3)} - {R(B3)} * Ω) * (1 - 9 / 100 / 5 * (10 / 3 * 0.6931471808)) := by
  unfold Qc; nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hb)]

theorem bkz7_poly{k} (Ω : ℝ) (ha : {R(a)} ≤ Ω) (hb : Ω ≤ {R(b)}) :
    Qc Ω (3 * 0.6931471808) < 8 * ({R(A7)} - {R(B7)} * Ω) * (1 - 3 / 10 / 5 * (10 / 3 * 0.6931471808)) := by
  unfold Qc; nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hb)]

theorem bksh_poly{k} (Ω : ℝ) (ha : {R(a)} ≤ Ω) (hb : Ω ≤ {R(b)}) :
    4 * ({R(C)} + {R(Dd)} * Ω) * Qc Ω (3 * 0.6931471808) <
      8 * ({R(A7)} - {R(B7)} * Ω) * Qc Ω (2 * 0.6931471803) * (1 - 18 / 100 / 5 * (10 / 3 * 0.6931471808)) := by
  have h1 : 0 ≤ Ω - {R(a)} := by linarith
  have h2 : 0 ≤ {R(b)} - Ω := by linarith
  unfold Qc
  nlinarith [mul_nonneg (mul_nonneg h1 h1) h1, mul_nonneg (mul_nonneg h1 h1) h2,
    mul_nonneg (mul_nonneg h1 h2) h2, mul_nonneg (mul_nonneg h2 h2) h2, mul_nonneg h1 h2]""")
head = """import Checked.Cosmography.B1Truncation

/-!
# Enclosures of the B1 distance integrals below the density one fifth (trust track T2b; run 2026-11-21T0628Z)

Lower bounds of the two distance integrals of `Checked.Cosmography.B1` (sources at redshift three and seven)
and upper bounds of the first, each linear in the density on one of five density pieces covering zero to one
fifth, by the lemmas `J_lower`, `J_upper`, `J_shift` of that module (right and left Riemann sums with tangent
and secant bounds of the inverse square root). The natural numbers below are hundred-thousandths, generated by
`runs/2026-11-21T0628Z/scripts/emit_bkcerts.py`; Lean checks them. The polynomial inequality of each piece
is what `Checked/Trust/NecessityBK.lean` needs for the two misses and their difference.
"""
head += "-/\n\nnamespace Checked.Trust.NCBKC\n\nopen Checked.Cosmography Checked.Cosmography.B1\n\n" + "\n".join(checks) + "\n\n"
print(head + "\n".join(data) + "\n" + "\n".join(lem) + "\n\nend Checked.Trust.NCBKC")
