"""Referee C15/C16: fresh derivation of flat d_L(z), d_A(z) to z^5 from a generic a(t).

a(t)/a0 = 1 + T - q T^2/2 + j T^3/6 + s T^4/24 + l T^5/120 + m T^6/720, T = H0 (t - t0)
(standard Visser convention: q = -a''a/a'^2, j = a'''a^2/a'^3, s = a''''a^3/a'^4, l = a^(5)a^4/a'^5).
Units H0 = c = a0 = 1. Past emission T < 0. 1+z = 1/a(T). chi = int_T^0 dT'/a(T').
d_L = (1+z) chi (flat), d_A = chi/(1+z) = d_L/(1+z)^2.
"""
import sympy as sp

T, z, q, j, s, l, m = sp.symbols('T z q j s l m')
N = 7

def trunc(e, x, n):
    e = sp.expand(e)
    return sum(e.coeff(x, k)*x**k for k in range(n))

def ser_inv(p, x, n):
    # 1/p for polynomial p with p(0)=1
    u = trunc(p - 1, x, n)
    r, pw = 1, 1
    for k in range(1, n):
        pw = trunc(pw*u, x, n)
        r += (-1)**k*pw
    return sp.expand(r)

def compose(p, x, sub, y, n):
    # p(x) polynomial, sub(y) with sub(0)=0
    r, pw = 0, 1
    for k in range(n):
        r += sp.expand(p).coeff(x, k)*pw
        pw = trunc(pw*sub, y, n)
    return trunc(r, y, n)
a = 1 + T - q*T**2/2 + j*T**3/6 + s*T**4/24 + l*T**5/120 + m*T**6/720
inv_a = ser_inv(a, T, N)
zT = sp.expand(inv_a - 1)
# chi(T) = int_T^0 1/a
chiT = sp.expand(-sp.integrate(inv_a, (T, 0, T)))
chiT = sum(chiT.coeff(T, k)*T**k for k in range(N))
# invert z(T) -> T(z)
Tz = 0
cs = [sp.Symbol('c%d' % k) for k in range(1, N)]
Tz_ans = sum(cs[k-1]*z**k for k in range(1, N))
eq = sp.expand(compose(zT, T, Tz_ans, z, N) - z)
sol = {}
for k in range(1, N):
    ck = sp.expand(eq.coeff(z, k).subs(sol))
    sk = sp.solve(ck, cs[k-1])[0]
    sol[cs[k-1]] = sp.expand(sk)
Tz = sp.expand(Tz_ans.subs(sol))
chiz = compose(chiT, T, Tz, z, N)
dL = trunc((1+z)*chiz, z, 6)
dA = trunc(chiz*ser_inv(1+z, z, 6), z, 6)


def coeffs(d):
    return [sp.factor(sp.expand(d.coeff(z, k+1))) for k in range(5)]


DL = coeffs(dL)
DA = coeffs(dA)
for k in range(5):
    print('D%d_L =' % k, sp.expand(120*DL[k]) if k == 4 else DL[k])
for k in range(5):
    print('D%d_A =' % k, sp.expand(120*DA[k]) if k == 4 else DA[k])

half = sp.Rational(1, 2)
# printed Demianski 2017 / Lusso 2019 (flat)
pDL = [1, -half*(-1+q), -sp.Rational(1, 6)*(1 - q - 3*q**2 + j),
       sp.Rational(1, 24)*(2 - 2*q - 15*q**2 - 15*q**3 + 5*j + 10*q*j + s),
       sp.Rational(1, 120)*(-6 + 6*q + 81*q**2 + 165*q**3 - 105*q**4 - 110*q*j - 105*q**2*j
                            - 15*q*s - 27*j + 10*j**2 - 11*s - l)]
pDA = [1, -half*(3+q), sp.Rational(1, 6)*(11 + 7*q + 3*q**2 - j),
       -sp.Rational(1, 24)*(50 + 46*q + 39*q**2 + 15*q**3 - 13*j - 10*q*j - s),
       sp.Rational(1, 120)*(274 + 326*q + 411*q**2 + 315*q**3 + 105*q**4 - 210*q*j
                            - 105*q**2*j - 15*q*s + 137*j + 10*j**2 - 21*s - l)]
for k in range(5):
    print('L%d correct-printed:' % k, sp.expand(DL[k]-pDL[k]),
          '  A%d correct-printed:' % k, sp.expand(DA[k]-pDA[k]))

# Convention probes: can any sign/normalisation of s, l (or j) make printed D4 correct?
S1, S2, S3 = sp.symbols('S1 S2 S3')
for name, sub in [('s->-s', {s: -s}), ('l->-l', {l: -l}), ('s,l->-s,-l', {s: -s, l: -l}),
                  ('j->-j', {j: -j}), ('q->-q', {q: -q})]:
    print(name, ' L4 diff:', sp.expand(DL[4].subs(sub, simultaneous=True) - pDL[4]),
          ' | A4 diff:', sp.expand(DA[4].subs(sub, simultaneous=True) - pDA[4]))

# y-series cross check: y = z/(1+z)
y = sp.symbols('y')
dLy = compose(dL, z, trunc(y*ser_inv(1-y, y, 6), y, 6), y, 6)
print('d_L(y) coeffs*:', [sp.expand(dLy.coeff(y, k)) for k in range(1, 6)])

# Consequence estimate: printed - correct D4_L = -(7/4) q^4 ; as a shift in l: dl = 210 q^4
for qq in [-0.5, -0.55, -0.6, -0.4, -0.7]:
    print('q0=%.2f  D4 error=%.5f  equivalent l0 shift=%.3f  (rel to D4 at LCDM Om=0.3: see below)'
          % (qq, -7/4*qq**4, 210*qq**4))
# LCDM flat Om=0.3 cosmographic parameters
Om = sp.Rational(3, 10)
qL = sp.Rational(3, 2)*Om - 1; jL = 1; sL = 1 - sp.Rational(9, 2)*Om; lL = 1 + 3*Om - sp.Rational(27, 2)*Om**2 * 1  # placeholder
# compute l directly from a(t) for LCDM via derivatives of H(z)
zz = sp.symbols('zz')
E = sp.sqrt(Om*(1+zz)**3 + 1 - Om)
dLex = trunc(sp.integrate(sp.series(1/E, zz, 0, 6).removeO(), (zz, 0, zz))*(1+zz), zz, 6)
print('LCDM exact d_L coeffs:', [sp.nsimplify(dLex.coeff(zz, k)) for k in range(1, 6)])
# fit q,j,s,l from exact LCDM by matching D1..D4
qs, js, ss, ls = sp.symbols('qs js ss ls')
eqs = [sp.Eq(DL[k].subs({q: qs, j: js, s: ss, l: ls}), dLex.coeff(zz, k+1)) for k in range(1, 5)]
sol2 = sp.solve(eqs, [qs, js, ss, ls], dict=True)
print('LCDM Om=0.3 (q,j,s,l):', sol2)
for so in sol2:
    vals = {q: so[qs], j: so[js], s: so[ss], l: so[ls]}
    print('  correct D4_L =', float(DL[4].subs(vals)), ' printed D4_L =', float(pDL[4].subs(vals)),
          ' correct D4_A =', float(DA[4].subs(vals)), ' printed D4_A =', float(pDA[4].subs(vals)))
    zv = 1.0
    print('  error at z=1 in d_L bracket, L:', float((pDL[4]-DL[4]).subs(vals))*zv**4,
          ' bracket total', float(sum(DL[k].subs(vals)*zv**k for k in range(5))))
