# Float study for hypothesis 1 (0 <= Omega) of B1Fit.fit_direction (run 2026-11-21T0828Z, for the next part 1 run).
# For Omega < 0 the farthest source (1+z = 4 sqrt2) is reachable only while Omega (1+z)^3 + 1 - Omega > 0, i.e.
# Omega > -1/((4 sqrt2)^3 - 1). Exact matching cubic (all three values positive, as hypotheses 14-16 require) and the
# conclusion margin; plus the worst case over the 0.05-mag box (vertices of the residual cube, offset free).
import mpmath as mp, itertools
mp.mp.dps = 30
l = mp.log(2); L10 = mp.log(10)
us = [l/2, 3*l/2, 5*l/2]
S = [mp.sqrt(2), 2*mp.sqrt(2), 4*mp.sqrt(2)]
def J(O, w):
    f = lambda v: 2/mp.sqrt(O+(1-O)*v**6)
    return mp.quad(f, [w, (w+1)/2, 1])
def concl(O, b2, b3):
    A2 = L10*(mp.mpf(3)/2 - mp.mpf(3)/4*O); A3 = L10**2*(mp.mpf(9)/8*O**2 - 2*O + mp.mpf(7)/6)
    return mp.mpf(20)/3*(l/L10)*(b3*L10**2 - A3) - (b2*L10 - A2 + mp.mpf(1)/2)
Omin = -1/((4*mp.sqrt(2))**3 - 1)
print('Omega_min', mp.nstr(Omin, 8))
for frac in ['0', '0.5', '0.9', '0.99', '0.999', '0.9999']:
    O = Omin*mp.mpf(frac)
    D = [S[i]*J(O, 1/mp.sqrt(S[i])) for i in range(3)]
    worst = None
    for e in itertools.product([-1, 1], repeat=3):
        k = [mp.mpf(10)**(mp.mpf(e[i])/100) for i in range(3)]  # +-0.05 mag
        M = mp.matrix([[us[i]**2, us[i]**3, -D[i]*k[i]] for i in range(3)])
        b2, b3, lam = mp.lu_solve(M, mp.matrix([-us[i] for i in range(3)]))
        m = concl(O, b2, b3)
        worst = m if worst is None or m < worst else worst
    print('Omega', mp.nstr(O, 6), 'J5/J3', mp.nstr(D[2]/D[1], 6), 'worst margin over the residual box', mp.nstr(worst, 6))
