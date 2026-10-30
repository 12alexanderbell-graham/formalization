"""Numeric checks of quoted LCDM-derived numbers in the log-polynomial literature.

Uses the flat-LCDM coefficients derived in derive_logpoly.py (re-derived here quickly, same method).
Run:  python3 check_numbers.py
"""
import sympy as sp

Om, z, u, w = sp.symbols('Omega_m z u w')
L10 = sp.log(10)
N = 5


def a_coeffs(E, n=N):
    chi = sp.integrate(sp.series(1 / E, z, 0, n).removeO(), (z, 0, z))
    dl = sp.series((1 + z) * chi, z, 0, n).removeO()
    dlu = sp.expand(sp.series(dl.subs(z, sp.exp(u) - 1), u, 0, n).removeO())
    return {k: sp.expand(dlu.coeff(u, k) * L10 ** (k - 1)) for k in range(1, n)}


aL = a_coeffs(sp.sqrt(Om * (1 + z) ** 3 + 1 - Om))

# --- Yang, Banerjee, O Colgain 2020 (1911.01681) Table 2 from their Table 1 (= Lusso+19 Table 2)
T1 = {'SNe, quasars, GRBs': (3.205, 0.165, 0.162, 3.564, 0.916, 0.938, -2.510, 1.510, 1.536),
      'SNe, quasars': (3.075, 0.172, 0.169, 4.466, 1.013, 1.040, -3.716, 1.922, 1.852),
      'SNe, GRBs': (3.304, 0.186, 0.183, 2.069, 1.122, 1.252, 2.571, 2.631, 2.506)}
print('Yang+20 Table 2 recomputed: Omega_m(a_n) real roots, and error = da/|da/dOm|')
for name, v in T1.items():
    out = []
    for k, (val, ep, em) in zip((2, 3, 4), (v[0:3], v[3:6], v[6:9])):
        roots = [complex(r) for r in sp.Poly(aL[k] - sp.Float(val), Om).nroots()]
        real = sorted(r.real for r in roots if abs(r.imag) < 1e-9)
        d = sp.diff(aL[k], Om)
        errs = [(round(ep / abs(float(d.subs(Om, r))), 3), round(em / abs(float(d.subs(Om, r))), 3)) for r in real]
        out.append((k, [round(r, 3) for r in real], errs))
    print(' ', name)
    for k, r, e in out:
        print(f'     a{k}: Omega_m roots {r}  errors(+,-) {e}')

# --- RL19 Fig 3 caption: wCDM magenta lines meet the LCDM curve at w = 1 (left) and w = -1 (right)?
E_w = sp.sqrt(Om * (1 + z) ** 3 + (1 - Om) * (1 + z) ** (3 * (1 + w)))
aw = a_coeffs(E_w, 4)
a2s, a3s = sp.symbols('a2 a3')
curve = 2 * a2s ** 2 - sp.Rational(10, 3) * L10 * a2s + sp.Rational(5, 3) * L10 ** 2 - a3s  # LCDM a3(a2)
res = sp.factor(sp.simplify(curve.subs({a2s: aw[2], a3s: aw[3]})))
print('\nRL19 Fig.3: LCDM-curve residual of the flat-wCDM point (a2(w),a3(w)) =', res)
print('   zeros in w:', sp.solve(res, w))
for Omv in (0.2, 0.3, 0.4, 0.5):
    print(f'   Om={Omv}: w=1 -> (a2,a3)=({float(aw[2].subs({Om:Omv,w:1})):.3f},{float(aw[3].subs({Om:Omv,w:1})):.3f})'
          f'  residual {float(res.subs({Om:Omv,w:1})):.3f};  w=0 -> ({float(aw[2].subs({Om:Omv,w:0})):.3f},'
          f'{float(aw[3].subs({Om:Omv,w:0})):.3f}) residual {float(res.subs({Om:Omv,w:0})):.3f}')

# RL19 Fig 3 black dot (Om=0.3) and curve vertex
print('\nLCDM Om=0.3: a2=%.4f a3=%.4f ; curve vertex a2=%.4f a3=%.4f' % (
    float(aL[2].subs(Om, 0.3)), float(aL[3].subs(Om, 0.3)),
    float(5 * L10 / 6), float(sp.Rational(5, 3) * L10 ** 2 - 2 * (5 * L10 / 6) ** 2)))
# RL19 Methods printed (no ln10) at Om=0.3, with the missing square
print('RL19 Methods as printed at Om=0.3: a2=%.4f  a3(7/6-2Om+9/8 Om)=%.4f' % (1.5 - 0.75 * 0.3, 7 / 6 - 2 * 0.3 + 9 / 8 * 0.3))

# --- Yang+20 (A.2) canonical values and (A.4) y-series
print('\nYang+20 (A.2) check: a2,a3,a4 at Om=0.3 =', [round(float(aL[k].subs(Om, 0.3)), 5) for k in (2, 3, 4)])
