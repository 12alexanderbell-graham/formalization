"""Per-piece constants (rho, m) for cubic_separation below the density one fifth (run 2026-11-21T0628Z).
Imports the enclosures of emit_bkcerts.py; prints Lean lemmas bksep_lin{k}, bksep_mq{k}, bksep_dd{k}
(appended to Checked/Trust/NecessityBK.lean by hand) and the region below zero."""
import sys, sympy as sp
from fractions import Fraction as Fr
sys.argv = ['x']
import importlib.util, io, contextlib
spec = importlib.util.spec_from_file_location('c', 'runs/2026-11-21T0628Z/scripts/emit_bkcerts.py')
c = importlib.util.module_from_spec(spec)
with contextlib.redirect_stdout(io.StringIO()):
    spec.loader.exec_module(c)
O = c.O; Qp = c.Qp; L2HI = c.L2HI; L2LO = c.L2LO; R = c.R
K = 1 - Fr(1, 10) / 5 * (Fr(10, 3) * L2HI)
L0 = (10 * L2LO - Fr(24, 1000)) / 3
def dd(rho, m):
    v = Fr(25, 16) * ((9 - 4 * rho)**2 * L2HI**4 / L0**2 + (27 - 8 * rho)**2 * L2HI**6 / L0**4)
    return v < m**2
out = []
def emit(tag, a, b, U, L, Us, Ls):
    # U, L: sympy linear in O (bounds of J3, J7); rho = floor(min 2 L K / U) at 4 digits
    r = min(sp.Rational(2) * L.subs(O, x) * K / U.subs(O, x) for x in (a, b))
    rho = Fr(int(r * 10000), 10000)
    mexpr = sp.expand(rho * Qp(2 * L2LO) - Qp(3 * L2HI))
    m = c.minon(mexpr, a, b)
    m = Fr(int(m * 10000), 10000)
    ok = m > 0 and dd(rho, m)
    print(f"-- {tag} [{a}, {b}]: rho {float(rho)}, m {float(m)}, ok {ok}", file=sys.stderr)
    assert ok
    out.append(f"""
theorem bksep_lin{tag} (Ω : ℝ) (ha : {R(a)} ≤ Ω) (hb : Ω ≤ {R(b)}) :
    {R(rho)} * ({Us}) ≤ 2 * ({Ls}) * (1 - 1 / 10 / 5 * (10 / 3 * 0.6931471808)) := by
  linarith

theorem bksep_mq{tag} (Ω : ℝ) (ha : {R(a)} ≤ Ω) (hb : Ω ≤ {R(b)}) :
    {R(m)} ≤ {R(rho)} * Qc Ω (2 * 0.6931471803) - Qc Ω (3 * 0.6931471808) := by
  unfold Qc; nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hb)]

theorem bksep_dd{tag} : (5 / 4 : ℝ) ^ 2 * ((9 - 4 * {R(rho)}) ^ 2 * 0.6931471808 ^ 4 /
        ((10 * 0.6931471803 - 24 / 1000) / 3) ^ 2
      + (27 - 8 * {R(rho)}) ^ 2 * 0.6931471808 ^ 6 / ((10 * 0.6931471803 - 24 / 1000) / 3) ^ 4)
      < {R(m)} ^ 2 := by norm_num""")
    return rho, m
res = {}
for k, (a, b) in enumerate(c.PIECES):
    A7, B7 = c.low[("7", k)]; C3, D3 = c.upp[k]
    U = sp.Rational(C3.numerator, C3.denominator) + sp.Rational(D3.numerator, D3.denominator) * O
    L = sp.Rational(A7.numerator, A7.denominator) - sp.Rational(B7.numerator, B7.denominator) * O
    res[k] = emit(str(k), a, b, U, L, f'{R(C3)} + {R(D3)} * Ω', f'{R(A7)} - {R(B7)} * Ω')
# below zero: J3 <= 33/10, J7 >= 544/81, for -1/511 <= Omega <= 0
res['n'] = emit('n', Fr(-1, 511), Fr(0), sp.Rational(33, 10) + 0 * O, sp.Rational(544, 81) + 0 * O, '(33 / 10 : ℝ)', '(544 / 81 : ℝ)')
print("\n".join(out))
for k, v in res.items(): print(f"-- {k}: rho = {v[0]}, m = {v[1]}")
