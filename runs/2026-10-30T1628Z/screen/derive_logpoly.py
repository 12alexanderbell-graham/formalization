"""First-principles derivation of log-polynomial and cosmographic coefficients.

d_L = (1+z) (c/H0) S_k( int_0^z dz'/E(z') ),  S_k(chi) = sinh(sqrt(Ok) chi)/sqrt(Ok).
Log-polynomial convention (RL19 / Lusso+19 / Bargiacchi+21 / Banerjee+21):
    d_L = ln(10) (c/H0) [ x + a2 x^2 + a3 x^3 + ... ],  x = log10(1+z)
With u = ln(1+z) = ln(10) x:  d_L/(c/H0) = sum_n b_n u^n  =>  a_n = b_n ln(10)^(n-1).

Run:  python3 derive_logpoly.py
"""
import sympy as sp

z, u, t, Om, Ok = sp.symbols('z u t Omega_m Omega_k')
q0, j0, s0, l0 = sp.symbols('q0 j0 s0 l0')
L10 = sp.log(10)
N = 6  # series order kept in u / z


def ser(e, v, n=N):
    return sp.series(e, v, 0, n).removeO()


# ---------------------------------------------------------------- flat LCDM in Omega_m
E = sp.sqrt(Om * (1 + z) ** 3 + 1 - Om)
chi = sp.integrate(ser(1 / E, z, N), (z, 0, z))            # comoving distance (c/H0=1)
dL_z = sp.expand(ser((1 + z) * chi, z, N))
dL_u = sp.expand(ser(dL_z.subs(z, sp.exp(u) - 1), u, N))  # z = e^u - 1
b = {n: sp.factor(dL_u.coeff(u, n)) for n in range(1, N)}
a_LCDM = {n: sp.expand(b[n] * L10 ** (n - 1)) for n in range(1, N)}
print('flat LCDM: b_n (coefficient of [ln(1+z)]^n);  a_n = b_n ln(10)^(n-1)')
for n in range(1, N):
    print(f'  b{n} =', sp.expand(b[n]))

# ---------------------------------------------------------------- general cosmography
# a(t)/a0 = 1 + t - q0 t^2/2 + j0 t^3/6 + s0 t^4/24 + l0 t^5/120  (H0=1, t = t - t0)
a_t = 1 + t - q0 * t ** 2 / 2 + j0 * t ** 3 / 6 + s0 * t ** 4 / 24 + l0 * t ** 5 / 120
# lookback: u = ln(1+z) = -ln a(t); invert series t(u) (t<0 in the past)
U_t = ser(-sp.log(a_t), t, N)
cs = sp.symbols('c1:%d' % N)
t_u = sum(cs[i] * u ** (i + 1) for i in range(N - 1))
eqs = sp.expand(ser(U_t.subs(t, t_u), u, N) - u)
sol = sp.solve([eqs.coeff(u, k) for k in range(1, N)], cs, dict=True)[0]
t_u = t_u.subs(sol)
# chi = int_t^0 dt'/a(t')  (c=1)
inv_a = ser(1 / a_t, t, N)
F = sp.integrate(inv_a, t)
chi_u = sp.expand(ser(-(F.subs(t, t_u)), u, N))
# curvature: S_k(chi) = chi + Ok chi^3/6 + Ok^2 chi^5/120
S = chi_u + Ok * chi_u ** 3 / 6 + Ok ** 2 * chi_u ** 5 / 120
dLgen_u = sp.expand(ser(sp.exp(u) * S, u, N))
B = {n: sp.expand(dLgen_u.coeff(u, n)) for n in range(1, N)}
print('\ngeneral cosmography: b_n in q0,j0,s0,l0,Omega_k')
for n in range(1, N):
    print(f'  b{n} =', B[n])

# z-series (check of Lusso+19 eqs 3-7, flat)
dLgen_z = sp.expand(ser(dLgen_u.subs(u, sp.log(1 + z)), z, N))
D = {n: sp.factor(dLgen_z.coeff(z, n + 1)) for n in range(0, N - 1)}
print('\nz-series d_L = z (D0 + D1 z + ...):')
for n in range(0, N - 1):
    print(f'  D{n} =', sp.expand(D[n]))

# consistency: LCDM cosmographic values reproduce the Omega_m result
lcdm = {q0: sp.Rational(3, 2) * Om - 1, j0: 1, s0: 1 - sp.Rational(9, 2) * Om,
        l0: 1 + 3 * Om + sp.Rational(27, 2) * Om ** 2, Ok: 0}
for n in range(1, N):
    assert sp.simplify(B[n].subs(lcdm) - b[n]) == 0, n
print('\n[ok] general cosmographic b_n reduce to flat-LCDM b_n with LCDM (q0,j0,s0,l0)')

# ---------------------------------------------------------------- printed formulas
chk = {}
# Lusso+19 eq (8) as printed
L19 = {2: L10 * (sp.Rational(3, 2) - sp.Rational(3, 4) * Om),
       3: L10 ** 2 * (sp.Rational(9, 8) * Om ** 2 - 2 * Om + sp.Rational(7, 6)),
       4: L10 ** 3 * (-sp.Rational(135, 64) * Om ** 3 + sp.Rational(18, 4) * Om ** 2
                      - sp.Rational(47, 16) * Om + sp.Rational(5, 8))}
for n, f in L19.items():
    chk[f'Lusso+19 eq8 a{n}'] = sp.simplify(f - a_LCDM[n])
# RL19 Methods (as printed, no ln10 factors)
RL = {2: sp.Rational(3, 2) - sp.Rational(3, 4) * Om,
      3: sp.Rational(7, 6) - 2 * Om + sp.Rational(9, 8) * Om ** 2}
for n, f in RL.items():
    chk[f'RL19 Methods a{n} (printed, no ln10)'] = sp.simplify(f - a_LCDM[n])
    chk[f'RL19 Methods a{n} == b{n} (natural-log coeff)'] = sp.simplify(f - b[n])
# eliminate Omega_m: a3 as function of a2 (flat LCDM)
a2s = sp.symbols('a2')
Om_of_a2 = sp.solve(sp.Eq(a2s, a_LCDM[2]), Om)[0]
a3_of_a2 = sp.expand(a_LCDM[3].subs(Om, Om_of_a2))
print('\nflat LCDM a3(a2) =', a3_of_a2)
chk['RL19 a3=5/3-10/3 a2+2a2^2 (printed)'] = sp.simplify(
    sp.Rational(5, 3) - sp.Rational(10, 3) * a2s + 2 * a2s ** 2 - a3_of_a2)
chk['RL19 a3(a2) with ln10->1 equals (a3/ln10^2)((a2/ln10))'] = sp.simplify(
    (sp.Rational(5, 3) - sp.Rational(10, 3) * a2s + 2 * a2s ** 2).subs(a2s, a2s / L10) * L10 ** 2
    - a3_of_a2)
chk['Banerjee+21 eq4 a3=(6a2^2-10a2 ln10+5ln10^2)/3'] = sp.simplify(
    (6 * a2s ** 2 - 10 * a2s * L10 + 5 * L10 ** 2) / 3 - a3_of_a2)
# Lusso+19 eqs (3)-(7)  (flat; D_L = cz/H0 (D0 + D1 z + ...))
L19D = {0: sp.Integer(1),
        1: -sp.Rational(1, 2) * (-1 + q0),
        2: -sp.Rational(1, 6) * (1 - q0 - 3 * q0 ** 2 + j0),
        3: sp.Rational(1, 24) * (2 - 2 * q0 - 15 * q0 ** 2 - 15 * q0 ** 3 + 5 * j0 + 10 * q0 * j0 + s0),
        4: sp.Rational(1, 120) * (-6 + 6 * q0 + 81 * q0 ** 2 + 165 * q0 ** 3 - 105 * q0 ** 4
                                  - 110 * q0 * j0 - 105 * q0 ** 2 * j0 - 15 * q0 * s0
                                  - 27 * j0 + 10 * j0 ** 2 - 11 * s0 - l0)}
for n, f in L19D.items():
    chk[f'Lusso+19 eq{n+3} D_L^{n} (flat)'] = sp.factor(sp.expand(f - D[n].subs(Ok, 0)))

print('\nprinted - derived (0 means AGREES):')
for k, v in chk.items():
    print(f'  {k}:  {v}')

# numbers at Omega_m = 0.3
print('\nflat LCDM, Omega_m=0.3:')
for n in range(2, N):
    print(f'  a{n} = {float(a_LCDM[n].subs(Om, 0.3)):.4f}   (b{n} = {float(b[n].subs(Om, 0.3)):.4f})')

# export for other scripts
if __name__ != '__main__':
    pass
