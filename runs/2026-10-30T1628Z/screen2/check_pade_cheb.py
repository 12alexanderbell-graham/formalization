# CDL 2019 (1904.01427v1): Chebyshev coefficients (193), rho numbers (199)-(202),
# Pade approximants (B.1)-(B.6), rational Chebyshev (C.1), (C.3), H21 (207).  H0 = 1.
import sympy as sp
z, q, j, s = sp.symbols('z q0 j0 s0')
dL = z*(1 + z/2*(1-q) - z**2/6*(1-q-3*q**2+j) + z**3/24*(2-2*q-15*q**2-15*q**3+5*j+10*q*j+s))  # (163), verified in check_series.py
# ---- Chebyshev coefficients of the degree-4 polynomial dL: exact projection (181)
x = sp.Symbol('x')
Tch = [sp.chebyshevt(n, z) for n in range(5)]
def to_cheb(poly):
    # exact Chebyshev coefficients of a polynomial (equals the projection (181) for polynomials)
    rem = sp.expand(poly); out = {}
    for d in range(sp.degree(rem, z), -1, -1):
        cd = sp.Poly(rem, z).coeff_monomial(z**d)
        out[d] = cd/(2**(d-1) if d > 0 else 1)
        rem = sp.expand(rem - out[d]*sp.chebyshevt(d, z))
    assert rem == 0
    return out
cc = to_cheb(dL)
cder = [sp.expand(cc[k]) for k in range(5)]
# spot-check projection integral (181) numerically for c2 at one parameter point
import math
from scipy.integrate import quad
pt = {q: -0.3, j: 0.7, s: 0.2}
g = sp.lambdify(z, dL.subs(pt))
c2num = 2/math.pi*quad(lambda th: g(math.cos(th))*math.cos(2*th), 0, math.pi)[0]
print('c2 projection integral numeric:', c2num, ' exact:', float(cder[2].subs(pt)))
cpr = [sp.Rational(1, 64)*(18+5*j*(1+2*q)-3*q*(6+5*q*(1+q))+s),
       sp.Rational(1, 8)*(7-j+q+3*q**2),
       sp.Rational(1, 48)*(14+5*j*(1+2*q)-q*(14+15*q*(1+q))+s),
       sp.Rational(1, 24)*(-1-j+q*(1+3*q)),
       sp.Rational(1, 192)*(2+5*j*(1+2*q)-q*(2+15*q*(1+q))+s)]
for k in range(5):
    print(f'c{k} printed - derived:', sp.expand(cpr[k]-cder[k]))
print('sum c_k T_k == dL:', sp.expand(sum(cpr[k]*Tch[k] for k in range(5)) - dL))
# ---- rational Chebyshev R_{n,m}: truncate c at T_{n+m}, match T_0..T_{n+m}
def rcheb(n, m, c):
    a = sp.symbols(f'a0:{n+1}'); b = sp.symbols(f'b1:{m+1}')
    num = sum(a[i]*sp.chebyshevt(i, z) for i in range(n+1))
    den = 1 + sum(b[i-1]*sp.chebyshevt(i, z) for i in range(1, m+1))
    f = sum(c[k]*sp.chebyshevt(k, z) for k in range(n+m+1))
    diff = sp.expand(den*f - num)
    # express diff in Chebyshev basis
    deg = sp.degree(diff, z)
    coeffs = {}
    rem = diff
    for d in range(deg, -1, -1):
        cd = sp.Poly(rem, z).coeff_monomial(z**d) if rem != 0 else 0
        coeffs[d] = cd/(2**(d-1) if d > 0 else 1)
        rem = sp.expand(rem - coeffs[d]*sp.chebyshevt(d, z))
    sol = sp.solve([coeffs[d] for d in range(n+m+1)], list(a)+list(b), dict=True)[0]
    return sp.simplify((num/den).subs(sol)), sol
R11, sol11 = rcheb(1, 1, cpr)
print('R11 b1 =', sp.factor(sol11[sp.Symbol('b1')]))
D48 = 14+5*j*(1+2*q)-q*(14+15*q*(1+q))+s
C8 = 7-j+q+3*q**2
C64 = 18+5*j*(1+2*q)-3*q*(6+5*q*(1+q))+s
C1pr = -((3*(2-2*q-15*q**2-15*q**3+5*j*(1+2*q)+s) + (1/C8)*(-72*C8**2 + 3*C64*D48 + 2*D48**2)*z)
         / (576*(1 - (D48*z)/(3*C8))))
print('(C.1) printed - derived:', sp.simplify(C1pr - R11))
R21, _ = rcheb(2, 1, cpr)
C3pr = ((-((3*(16*(-1-j+q+3*q**2)*(7-j+q+3*q**2) - C64*D48))/D48)
         + 4*(47-j+q+3*q**2 - (12*(-1+q)*(1+j-q*(1+3*q)))/D48)*z
         - (4*(12*(-1-j+q+3*q**2)*(7-j+q+3*q**2) + 4*(1+j-q*(1+3*q))**2 - D48**2)*(-1+2*z**2))/D48)
        / (192*(1 + (4*(1+j-q*(1+3*q))*z)/D48)))
print('(C.3) printed - derived:', sp.simplify(C3pr - R21))
# ---- (199), (202)
lc = {q: sp.Rational(-55, 100), j: 1, s: sp.Rational(-35, 100)}
rhoR = sp.Abs(-3*C8/D48).subs(lc)
print('rho_R11 (199) at (195):', sp.N(rhoR, 6), ' 1/|b1| derived:', sp.N(sp.Abs(1/sol11[sp.Symbol("b1")]).subs(lc), 6))
print('rho_P11 2/(1-q0):', sp.N((2/(1-q)).subs(lc), 6), ' rho_dL2 (1-q0)/2:', sp.N(((1-q)/2).subs(lc), 6))
# ---- Pade (B.1)-(B.6): check P - dL = O(z^{n+m+1})
B = {
 (1, 1): 2*z/(2+(-1+q)*z),
 (1, 2): 12*z/(12+6*(-1+q)*z+(5+2*j-q*(8+3*q))*z**2),
 (2, 1): z*(6*(-1+q)+(-5-2*j+q*(8+3*q))*z)/(-2*(3+z+j*z)+2*q*(3+z+3*q*z)),
 (1, 3): 24*z/(24+12*(-1+q)*z+2*(5+2*j-q*(8+3*q))*z**2-(9+j*(9+6*q)-q*(19+2*q*(7+3*q))+s)*z**3),
 (2, 2): (6*z*(10+9*z-6*q**3*z+s*z-2*q**2*(3+7*z)-q*(16+19*z)+j*(4+(9+6*q)*z)))/
         (60+24*z+6*s*z-2*z**2+4*j**2*z**2-9*q**4*z**2-3*s*z**2+6*q**3*z*(-9+4*z)+q**2*(-36-114*z+19*z**2)
          +j*(24+6*(7+8*q)*z+(-7-23*q+6*q**2)*z**2)+q*(-96-36*z+(4+3*s)*z**2)),
 (3, 1): (z*(24*(1+j-q*(1+3*q))+6*(4+j*(7+8*q)-q*(6+q*(19+9*q))+s)*z
          +(2-4*j**2+j*(7+(23-6*q)*q)+q*(-4+q*(-19+3*q*(-8+3*q))-3*s)+3*s)*z**2))/
         (24*(1+j-q*(1+3*q))+6*(2+5*j*(1+2*q)-q*(2+15*q*(1+q))+s)*z),
}
for (n, m), P in B.items():
    d = sp.series(P - dL, z, 0, n+m+2).removeO()
    low = [sp.simplify(d.coeff(z, k)) for k in range(n+m+1)]
    print(f'P{n},{m}: coeffs z^0..z^{n+m} of (P - dL):', low, '| z^{n+m+1}:', sp.factor(d.coeff(z, n+m+1)) != 0)
# ---- (207) H21 from P21 via (164): H = [d/dz (dL/(1+z))]^{-1}
H21der = sp.simplify(1/sp.diff(B[(2, 1)]/(1+z), z))
H21pr = (2*(1+z)**2*(3+z+j*z-q*(3+z+3*q*z))**2) / (18*(q-1)**2 + 6*(q-1)*(-5-2*j+q*(8+3*q))*z
        + (14+2*j**2+j*(7-q*(10+9*q))+q*(-40+q*(17+9*q*(2+q))))*z**2)
print('(207) printed - [d/dz(P21/(1+z))]^-1:', sp.simplify(H21pr - H21der))
# Is (207) itself the (2,1) Pade of H(z)? compare Taylor to z^3 with correct H series
Hc = 1 + (1+q)*z + (j-q**2)*z**2/2 + (3*q**2+3*q**3-j*(3+4*q)-s)*z**3/6
print('(207) - H Taylor through z^2:', [sp.simplify(sp.series(H21pr - Hc, z, 0, 3).removeO().coeff(z, k)) for k in range(3)])
