# CS 2009 Eqs. (32)-(38): r0(D) = (D/a0){sum R^n (H0 D)^n}, D = c (t0 - t); H0 = a0 = c = 1, k = K
import sympy as sp
D, tau = sp.symbols('D tau'); q, j, s, l, k = sp.symbols('q j s l k')
a = 1 + tau - q*tau**2/2 + j*tau**3/6 + s*tau**4/24 + l*tau**5/120
inva = sp.series(1/a, tau, 0, 7).removeO()
chi = sp.expand(-sp.integrate(inva, tau).subs(tau, -D))  # int_{-D}^0 dt/a
chi = sum(chi.coeff(D, i)*D**i for i in range(8))
r = sp.expand(chi - k*chi**3/6 + k**2*chi**5/120)
R = [sp.expand(r.coeff(D, n+1)) for n in range(6)]
printed = [1, sp.Rational(1, 2), (2 + q - k)/6, (6 + 6*q + j - 6*k)/24,
           (24 + 36*q + 6*q**2 + 8*j - s - 5*k*(7 + 2*q))/120,
           (24 + 48*q + 18*q**2 + 4*q*j + 12*j - 2*s + 24*l - 3*k*(15 + 10*q + j))/144]
for n in range(6):
    print(f"R^{n}_D: true - printed = {sp.factor(R[n] - printed[n])}")
print("true R^5_D (k=0) * 720 =", sp.expand(720*R[5].subs(k, 0)))
print("printed R^5_D (k=0) * 720 =", sp.expand(720*printed[5].subs(k, 0)))
print("true R^5_D k-part * 720 =", sp.factor(sp.expand(720*(R[5]-R[5].subs(k, 0)))))
