import sympy as sp

# Units: c = 1, H0 = 1 (so d_H = 1). Scale factor a(t) around t0 (tau = t - t0 <= 0).
tau, q0, j0, s0, z, y, k, a0 = sp.symbols('tau q0 j0 s0 z y k a0')
N = 5
# a(t)/a0 = 1 + tau - q0/2 tau^2 + j0/6 tau^3 + s0/24 tau^4
A = 1 + tau - q0/2*tau**2 + j0/6*tau**3 + s0/24*tau**4
# 1+z = a0/a(t_emit)
onepz = sp.series(1/A, tau, 0, N).removeO()
# comoving coordinate distance: r_c = a0 * int_t^t0 dt/a  -> chi = int_tau^0 dt/A
u = sp.symbols('u')
invA = sp.series(1/A.subs(tau, u), u, 0, N).removeO()
chi = sp.integrate(invA, (u, tau, 0))
chi = sp.expand(chi)
# invert z(tau): find tau(z) series
zt = sp.expand(onepz - 1)
# series reversion
T = sp.symbols('T')
c = sp.symbols('c1:6')
ansatz = sum(c[i]*z**(i+1) for i in range(4))
eq = sp.expand(sp.series(zt.subs(tau, ansatz), z, 0, 5).removeO() - z)
sol = sp.solve([eq.coeff(z, n) for n in range(1, 5)], c[:4], dict=True)[0]
tauz = ansatz.subs(sol)
chiz = sp.expand(sp.series(chi.subs(tau, tauz), z, 0, 5).removeO())
# curvature: physical transverse distance a0 * S_k(chi_c) with chi in units a0: r = a0 sin(sqrt(k) chi/a0)/sqrt(k)
# a0 dimensionless here (H0 = c = 1). S = chi - k chi^3/(6 a0^2) + ...
Om = sp.symbols('Omega0')
# k/a0^2 = Om - 1  (since d_H = 1)
S = chiz - (Om - 1)*chiz**3/6
S = sp.expand(sp.series(S, z, 0, 5).removeO())
dL = sp.expand(sp.series((1+z)*S, z, 0, 5).removeO())
print('d_L(z) =', sp.collect(dL, z))
print('d_L(z) coeff z^3 *(-6):', sp.factor(-6*dL.coeff(z, 3)))
# y-variable: z = y/(1-y), 1+z = 1/(1-y)
def yser(expr, n=5):
    return sp.expand(sp.series(expr.subs(z, y/(1-y)), y, 0, n).removeO())
dLy = yser(dL)
results = {}
for name, p in [('d_L', 0), ('d_F', sp.Rational(1, 2)), ('d_P', 1), ('d_Q', sp.Rational(3, 2)), ('d_A', 2)]:
    e = yser(dL*(1+z)**(-p)) if p != 0 else dLy
    e = sp.expand(sp.series(dL.subs(z, y/(1-y))*(1-y)**p, y, 0, 4).removeO())
    br = sp.expand(e/y)
    print(f'{name}(y)/y : 1 + ({sp.factor(br.coeff(y,1))}) y + ({sp.factor(br.coeff(y,2))}) y^2')
    print(f'    y^2 coeff * 24 = {sp.expand(24*br.coeff(y,2))}; *12 = {sp.expand(12*br.coeff(y,2))}; *6 = {sp.expand(6*br.coeff(y,2))}')
    results[name] = br
# Paper's (59)
paper59 = 1 - q0/2*y + sp.Rational(1, 12)*(3 - 2*q0 + 12*q0**2 - 4*(j0+Om))*y**2
corr = 1 - q0/2*y + sp.Rational(1, 24)*(3 - 2*q0 + 12*q0**2 - 4*(j0+Om))*y**2
print('derived - paper59 :', sp.factor(sp.expand(results['d_Q'] - paper59)))
print('derived - 1/24 ver:', sp.expand(results['d_Q'] - corr))
# ln(d_Q/(d_H y)) series
lnQ = sp.expand(sp.series(sp.log(results['d_Q']), y, 0, 3).removeO())
print('ln(d_Q/(d_H y)) =', sp.collect(lnQ, y), ' y^2 coeff*24:', sp.expand(24*lnQ.coeff(y,2)))
# de Sitter flat check: q0=-1, j0=1, Om=1
print('dS d_Q y^2 coeff:', results['d_Q'].coeff(y,2).subs({q0:-1, j0:1, Om:1}))
print('paper59 dS y^2 coeff:', paper59.coeff(y,2).subs({q0:-1, j0:1, Om:1}))
# Einstein-de Sitter: q0=1/2, j0=1, Om=1: d_L = 2 d_H (1+z)(1 - 1/sqrt(1+z))
EdS = 2*(1+z)*(1 - 1/sp.sqrt(1+z))
eds_Q = sp.series((EdS*(1+z)**sp.Rational(-3, 2)).subs(z, y/(1-y)), y, 0, 4)
print('EdS exact d_Q(y):', eds_Q)
print('derived EdS:', sp.expand(y*results['d_Q'].subs({q0: sp.Rational(1, 2), j0: 1, Om: 1})))
print('paper59 EdS:', sp.expand(y*paper59.subs({q0: sp.Rational(1, 2), j0: 1, Om: 1})))
