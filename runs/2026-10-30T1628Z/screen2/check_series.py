# First-principles checks of CDL 2019 (arXiv:1904.01427v1) Sec. 5 kinematic formulas.
import sympy as sp
z, t, q, j, s, l, H0 = sp.symbols('z t q0 j0 s0 l0 H0')
# flat FLRW: a(t) Taylor with H0=1 (restore later), a(t0)=1
T = sp.Symbol('T')  # T = t - t0
a = 1 + T - q*T**2/2 + j*T**3/6 + s*T**4/24 + l*T**5/120
N = 6
# z(T) = 1/a - 1 ; invert to T(z)
zT = sp.series(1/a - 1, T, 0, N).removeO()
# invert series
Tz = 0
cs = sp.symbols('c1:7')
trial = sum(cs[i]*z**(i+1) for i in range(N-1))
eq = sp.expand(sp.series(zT.subs(T, trial), z, 0, N).removeO() - z)
sol = sp.solve([eq.coeff(z, k) for k in range(1, N)], cs[:N-1], dict=True)[0]
Tz = trial.subs(sol)
# H(z) = adot/a
adot = sp.diff(a, T)
Hz = sp.series((adot/a).subs(T, Tz), z, 0, 4).removeO()
Hz = sp.expand(Hz)
print('H(z)/H0 coefficients (z^k * k!):')
for k in range(4):
    print(k, sp.factor(Hz.coeff(z, k)*sp.factorial(k)))
H3_correct = sp.expand(Hz.coeff(z, 3)*6)
H3_printed_165d = 3*q**2 + 3*q**3 - j*(3+4*q) - s
H3_printed_246 = -3*q**2 - 3*q**3 + j*(3+4*q) + s
print('(165d)/(204) printed - correct:', sp.expand(H3_printed_165d - H3_correct))
print('(246) printed - correct:', sp.expand(H3_printed_246 - H3_correct))
# dL flat = (1+z) * int_0^z dz'/H
chi = sp.integrate(sp.series(1/Hz, z, 0, 4).removeO(), (z, 0, z))
dL = sp.expand(sp.series((1+z)*chi, z, 0, 5).removeO())
dL163 = z*(1 + z/2*(1-q) - z**2/6*(1-q-3*q**2+j) + z**3/24*(2-2*q-15*q**2-15*q**3+5*j+10*q*j+s))
print('(163) printed - correct:', sp.expand(dL163 - dL))
# LCDM check of H3 sign
Om = sp.Symbol('Om')
E = sp.sqrt(Om*(1+z)**3 + 1 - Om)
E3 = sp.simplify(sp.diff(E, z, 3).subs(z, 0))
lc = {q: -1 + sp.Rational(3, 2)*Om, j: 1, s: 1 - sp.Rational(9, 2)*Om}
print('LCDM E3 exact:', sp.factor(E3), ' correct-formula:', sp.factor(H3_correct.subs(lc)), ' printed(204):', sp.factor(H3_printed_165d.subs(lc)))
print('LCDM Om=0.3 numbers: E3 exact', E3.subs(Om, 0.3), ' printed (204)', H3_printed_165d.subs(lc).subs(Om, 0.3))
# LCDM q,j,s (194)
a_ = sp.Function('a')
# use H(z) exact: q = -1 + (1+z)H'/H ; j, s via d/dt = -(1+z)H d/dz
Hs = E
qz = -1 + (1+z)*sp.diff(Hs, z)/Hs
# a''' /(aH^3): use j = q(2q+1) + (1+z) dq/dz ; s = -j(2+3q) - (1+z) dj/dz  (conventional identities, verified below)
jz = qz*(2*qz+1) + (1+z)*sp.diff(qz, z)
sz = -jz*(2+3*qz) - (1+z)*sp.diff(jz, z)
print('LCDM q0,j0,s0:', [sp.simplify(e.subs(z, 0)) for e in (qz, jz, sz)])
# (166)-(168): check against definitions with generic H(t)
tt = sp.Symbol('t'); Hf = sp.Function('H')(tt)
A = sp.exp(sp.integrate(Hf, tt)) if False else None
# a'/a = H -> a''/a = Hdot + H^2, a'''/a = Hddot + 3 H Hdot + H^3, a''''/a = Hdddot + 4 H Hddot + 3 Hdot^2 + 6 H^2 Hdot + H^4
Hd, Hdd, Hddd, h = sp.symbols('Hd Hdd Hddd h')
q_true = -(Hd + h**2)/h**2
j_true = (Hdd + 3*h*Hd + h**3)/h**3
s_true = (Hddd + 4*h*Hdd + 3*Hd**2 + 6*h**2*Hd + h**4)/h**4
q166 = -1 - Hd/h
j167 = 1 + (Hd + Hdd)/h**2
s168 = 1 + 2/h**2*(3*Hd + 2*Hdd) + (3*h**2 + Hddd)/h**4
for nm, pr, tr in (('166', q166, q_true), ('167', j167, j_true), ('168', s168, s_true)):
    print(nm, 'printed - true =', sp.simplify(pr - tr), '| at h=1:', sp.simplify((pr - tr).subs(h, 1)))
# verify the a-derivative identities used for s_true against a concrete a(t)
a_t = sp.exp(tt**2/3 + tt)  # arbitrary
Hc = sp.diff(a_t, tt)/a_t
chk = sp.simplify(sp.diff(a_t, tt, 4)/a_t - s_true.subs({Hddd: sp.diff(Hc, tt, 3), Hdd: sp.diff(Hc, tt, 2), Hd: sp.diff(Hc, tt), h: Hc})*Hc**4)
print('identity check s:', chk)
