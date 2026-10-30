"""Cross-checks for the y = z/(1+z) coefficients (Eqs. 10.52-10.63) of arXiv:1205.3421.
(a) Internal consistency: re-expand the paper's OWN printed z-coefficients (10.39-10.44, 10.46-10.51)
    in y, with Kc^2/(H0^2 a0^2) = Omega0 - 1 (paper's own definition on p.110), and compare to the
    printed y-coefficients.  Removes any dependence on my derivation of the z-series.
(b) Exact Milne universe (a ~ t, K=-1): q=j=s=l=0, Kc^2/(H0^2a0^2) = -1, Omega0 = 0,
    d_L = (c/H0) z (1+z/2), d_A = d_L/(1+z)^2, both exactly.
"""
import sympy as sp
q, j, s, l, O, Ok, y, z = sp.symbols('q0 j0 s0 l0 Omega0 Ok y z')
N = 6
def trunc(e, v, n=N):
    e = sp.expand(e); return sum(e.coeff(v, k)*v**k for k in range(n))

DLp = [1, -(-1+q)/2, -(1-q-3*q**2+j+Ok)/6,
       (2-2*q-15*q**2-15*q**3+5*j+10*q*j+s+2*Ok*(1+3*q))/24,
       (-6+6*q+81*q**2+165*q**3+105*q**4-110*q*j-105*q**2*j-15*q*s
        - 27*j+10*j**2-11*s-l-5*Ok*(1+8*q+9*q**2-2*j))/120]
DAp = [1, -(3+q)/2, (11+7*q+3*q**2-j-Ok)/6,
       -(50+46*q+39*q**2+15*q**3-13*j-10*q*j-s-2*Ok*(5+3*q))/24,
       (274+326*q+411*q**2+315*q**3+105*q**4-210*q*j-105*q**2*j-15*q*s
        - 137*j+10*j**2-21*s-l-5*Ok*(17+20*q+9*q**2-2*j))/120]
DLyp = [1, -(-3+q)/2, -(12-5*q+3*q**2-j-O)/6,
        (52-20*q+21*q**2-15*q**3-7*j+10*q*j+s-2*O*(1+3*q))/24,
        (359-184*q+186*q**2-135*q**3+105*q**4+90*q*j-105*q**2*j-15*q*s
         - 57*j+10*j**2+9*s-l-5*O*(17-6*q+9*q**2-2*j))/120]
DAyp = [1, -(1+q)/2, -(-q-3*q**2+j+O)/6,
        -(-2*q+3*q**2+15*q**3-j-10*q*j-s+2*O)/24,
        -(1-6*q+9*q**2-15*q**3-105*q**4+10*q*j+105*q**2*j+15*q*s
          - 3*j-10*j**2+s+l+5*O)/120]

zy = sum(y**k for k in range(1, N+1))  # z = y/(1-y)
def toy(coeffs):
    e = sum(c*z**(k+1) for k, c in enumerate(coeffs))
    e = trunc(sp.expand(e.subs(z, zy)), y)
    return [sp.expand(e.coeff(y, k+1).subs(Ok, O-1)) for k in range(5)]

print('(a) internal consistency: printed y-coeff  minus  y-re-expansion of printed z-coeffs')
for nm, zc, yc in [('D_L,y', DLp, DLyp), ('D_A,y', DAp, DAyp)]:
    yy = toy(zc)
    for k in range(5):
        d = sp.factor(sp.expand(yc[k] - yy[k]))
        print(f'  {nm}^{k}: {d}')

print('\n(b) Milne universe check (exact coefficients vs printed vs printed-z):')
milne = {q: 0, j: 0, s: 0, l: 0, O: 0, Ok: -1}
dLz = sp.series(z*(1+z/2), z, 0, 6).removeO()
dLy = sp.series((y/(1-y))*(1+y/(2*(1-y))), y, 0, 6).removeO()
dAz = sp.series(z*(1+z/2)/(1+z)**2, z, 0, 6).removeO()
dAy = sp.series((y/(1-y))*(1+y/(2*(1-y)))*(1-y)**2, y, 0, 6).removeO()
for nm, exact, v, pr in [('D_L', dLz, z, DLp), ('D_A', dAz, z, DAp), ('D_L,y', dLy, y, DLyp), ('D_A,y', dAy, y, DAyp)]:
    ex = [sp.expand(exact).coeff(v, k+1) for k in range(5)]
    pv = [sp.nsimplify(sp.sympify(c).subs(milne)) for c in pr]
    print(f'  {nm}: exact {ex}  printed {pv}')
