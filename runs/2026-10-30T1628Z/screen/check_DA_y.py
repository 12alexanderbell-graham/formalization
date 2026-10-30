"""z-series of d_A = d_L/(1+z)^2 and y-series of d_L (y = z/(1+z)), general cosmography + curvature.
Checks Demianski+17b (1609.09631) eqs (13)-(23) and Yang+20 (1911.01681) eqs (A.4)-(A.5).
Run: python3 check_DA_y.py   (imports the derivation from derive_logpoly.py by exec; slow ~1 min)
"""
import sympy as sp, io, contextlib, pathlib
ns = {}
with contextlib.redirect_stdout(io.StringIO()):
    exec(pathlib.Path(__file__).with_name('derive_logpoly.py').read_text(), ns)
z, u, q0, j0, s0, l0, Ok = (ns[k] for k in ('z', 'u', 'q0', 'j0', 's0', 'l0', 'Ok'))
dLz = ns['dLgen_z']
dAz = sp.expand(sp.series(dLz / (1 + z) ** 2, z, 0, 6).removeO())
DA = {n: sp.expand(dAz.coeff(z, n + 1)) for n in range(5)}
for n in range(5):
    print(f'D_A^{n} =', DA[n])
printed = {1: -sp.Rational(1, 2) * (3 + q0),
           2: sp.Rational(1, 6) * (11 + 7 * q0 + 3 * q0 ** 2 - j0),
           3: -sp.Rational(1, 24) * (50 + 46 * q0 + 39 * q0 ** 2 + 15 * q0 ** 3 - 13 * j0 - 10 * q0 * j0 - s0),
           4: sp.Rational(1, 120) * (274 + 326 * q0 + 411 * q0 ** 2 + 315 * q0 ** 3 + 105 * q0 ** 4 - 210 * q0 * j0
                                     - 105 * q0 ** 2 * j0 - 15 * q0 * s0 + 137 * j0 + 10 * j0 ** 2 - 21 * s0 - l0)}
print('\nDemianski+17b printed D_A^n - derived (flat part, Omega_k=0):')
for n, f in printed.items():
    print(f'  D_A^{n}:', sp.factor(sp.expand(f - DA[n].subs(Ok, 0))))
print('  curvature part of derived D_A^3:', sp.factor(DA[3] - DA[3].subs(Ok, 0)), '  (Omega_k = -k c^2/(H0^2 a0^2))')
# y-series of d_L
y = sp.symbols('y')
dLy = sp.expand(sp.series(dLz.subs(z, y / (1 - y)), y, 0, 4).removeO())
C1, C2 = dLy.coeff(y, 2), dLy.coeff(y, 3)
print('\nYang+20 (A.4): C1 =', sp.factor(C1), ' C2 =', sp.factor(C2.subs(Ok, 0)), '(flat)')
print('  C1 printed - derived:', sp.simplify(sp.Rational(1, 2) * (3 - q0) - C1))
print('  C2 printed - derived (flat):', sp.simplify(sp.Rational(1, 6) * (11 - 5 * q0 + 3 * q0 ** 2 - j0) - C2.subs(Ok, 0)))
v = {q0: sp.Rational(-55, 100), j0: 1, Ok: 0}
print('  (A.5) at (q0,j0)=(-0.55,1): C1 =', sp.N(C1.subs(v), 8), ' C2 =', sp.N(C2.subs(v), 8), '  printed 1.775, 2.27652')
