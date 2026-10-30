"""Independent sympy check for C1 (Cattoen-Visser d_Q(y)) and C3 (Capozziello-Cardone-Salzano App. A).

Units: H0 = 1, c = 1, a(t0) normalised so A(tau) = a/a0, tau = H0 (t - t0).
A(tau) = 1 + tau - q/2 tau^2 + j/6 tau^3 + s/24 tau^4 + l/120 tau^5  (Eq. A1 of 0802.1583; same def as C&V)
eps2 = k c^2/(a0^2 H0^2)  (C&V: Omega0 = 1 + eps2)
"""
import sympy as sp

q, j, s, l, eps2, tau, x, z, y = sp.symbols('q0 j0 s0 l0 eps2 tau x z y')
N = 7
A = 1 + tau - q/2*tau**2 + j/6*tau**3 + s/24*tau**4 + l/120*tau**5

def trunc(e, v, n):
    p = sp.Poly(sp.expand(e), v)
    return sum(c*v**m[0] for m, c in zip(p.monoms(), p.coeffs()) if m[0] < n)

def inv(e, v, n):
    # 1/e for e = 1 + O(v), truncated below v^n
    u = trunc(e - 1, v, n); r = 1; p = 1
    for k in range(1, n):
        p = trunc(p*(-u), v, n); r += p
    return sp.expand(r)

def ser(e, v, n):
    return trunc(e, v, n)

# ---------- comoving integral I(x) = int_{-x}^0 dtau / A(tau)
invA = inv(A, tau, N)
I = sp.expand(sp.integrate(invA, (tau, -x, 0)))

# ---------- C3: D(z), D = c (t0 - t*) = x (in c/H0 units).  1/(1+z) = A(-x)
zx = inv(A.subs(tau, -x), x, N) - 1          # z as series in x
# invert: x = sum c_n z^n
cs = sp.symbols('c1:7')
xz = sum(cs[i]*z**(i+1) for i in range(6))
eqn = None
# order-by-order inversion of z = zx(x)
xz = z
for n in range(2, 7):
    resid = trunc(sum(sp.Poly(zx, x).coeff_monomial(x**m) * trunc(xz**m, z, 7) for m in range(1, 7)), z, n+1) - z
    xz = sp.expand(xz - sp.Poly(resid, z).coeff_monomial(z**n) * z**n)
print("C3  D(z)/(cz/H0) coefficients D_z^n:")
Dz = {}
for n in range(0, 5):
    Dz[n] = sp.expand(sp.Poly(xz, z).coeff_monomial(z**(n+1)))
    print(f"  D_z^{n} =", Dz[n])
printed_Dz4 = (1 + 2*q + 3*q**2 + sp.Rational(5,2)*q**3 + sp.Rational(7,2)*q**4
               - sp.Rational(5,3)*q*j - sp.Rational(7,8)*q**2*j - j + j**2/12
               - sp.Rational(1,8)*q*s - s/6 - l/120)
print("  printed D_z^4 - derived =", sp.expand(printed_Dz4 - Dz[4]))
printed_Dz3 = -(1 + sp.Rational(3,2)*q + sp.Rational(3,2)*q**2 + sp.Rational(5,8)*q**3
                - j/2 - sp.Rational(5,12)*q*j - s/24)
print("  printed D_z^3 - derived =", sp.expand(printed_Dz3 - Dz[3]))

# ---------- C3: r0(D)/(D/a0) as series in x = H0 D/c ; S_k(chi), chi = sqrt? use eps2 = k c^2/(a0^2 H0^2)
# a0 r0 / D = [eps I - k eps^3 I^3/6 + k^2 eps^5 I^5/120]/(eps x) with k^2=1 for k=+-1 -> eps2 I^3, eps2^2 I^5
R = ser((I - eps2*I**3/6 + eps2**2*I**5/120)/x, x, 6)
print("C3  r0/(D/a0) coefficients R_D^n:")
for n in range(0, 6):
    print(f"  R_D^{n} =", sp.factor_terms(sp.expand(sp.Poly(R, x).coeff_monomial(x**n))))
printed_R5 = (24 + 48*q + 18*q**2 + 4*q*j + 12*j - 2*s + 24*l)/144 - 3*eps2*(15 + 10*q + j)/144
print("  printed R_D^5 - derived =", sp.expand(printed_R5 - sp.Poly(R, x).coeff_monomial(x**5)))
printed_R4 = (24 + 36*q + 6*q**2 + 8*j - s - 5*eps2*(7 + 2*q))/120
print("  printed R_D^4 - derived =", sp.expand(printed_R4 - sp.Poly(R, x).coeff_monomial(x**4)))

# ---------- C1: Cattoen-Visser.  chi(z) = I(x(z)), d_L = (1+z) S_k(chi)/sqrt-free form, units d_H
# only need d_L to z^3: truncate inputs to keep expansion small
I4 = trunc(I, x, 5); xz4 = trunc(xz, z, 5)
chi_z = trunc(sum(sp.Poly(I4, x).coeff_monomial(x**m) * trunc(xz4**m, z, 5) for m in range(1, 5)), z, 5)
dL = ser((1 + z)*(chi_z - eps2*trunc(chi_z**3, z, 5)/6), z, 4)
print("C1  d_L(z)/d_H =", sp.collect(dL, z))
Om0 = sp.symbols('Omega0')
dQ_z = ser(dL*sp.series((1 + z)**sp.Rational(-3, 2), z, 0, 5).removeO(), z, 4)
dQ_y = ser(dQ_z.subs(z, sum(y**m for m in range(1,6))), y, 4)
c2 = sp.expand(sp.Poly(dQ_y, y).coeff_monomial(y**3)).subs(eps2, Om0 - 1)
print("C1  d_Q(y)/(d_H y): y^1 coeff =", sp.Poly(dQ_y, y).coeff_monomial(y**2),
      "; y^2 coeff =", sp.factor(c2))
print("     24*coeff =", sp.expand(24*c2), "  12*coeff =", sp.expand(12*c2))
c2z = sp.expand(sp.Poly(dQ_z, z).coeff_monomial(z**3)).subs(eps2, Om0 - 1)
print("C1  d_Q(z): 24 * z^2 coeff =", sp.expand(24*c2z), " (C&V 0809.0537 Eq.17 prints 27+22q0+12q0^2-4(j0+Omega0))")
