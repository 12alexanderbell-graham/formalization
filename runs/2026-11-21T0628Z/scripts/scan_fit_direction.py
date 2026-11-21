# Float study for the open hypotheses 13-16 of B1Fit.fit_direction (run 2026-11-21T0628Z, for the next part 1 run).
# Sources 1+z = sqrt2, 2 sqrt2, 4 sqrt2 (u = l/2, 3l/2, 5l/2, l = ln 2). A cubic P(u) = u + b2 u^2 + b3 u^3 matches
# the three distances up to a common offset exactly iff (P1, P3, P5) = lam * (s1 D1, s3 D3, s5 D5) for signs s
# (Lean's logb reads |x|); dropping hp_i allows s_i = -1, dropping 0 < H allows all three negative.
# Conclusion: a2 - A2 + 1/2 < (20/3) log10(2) (a3 - A3), with a2 = b2 ln10, a3 = b3 ln10^2.
import mpmath as mp, itertools
mp.mp.dps = 30
l = mp.log(2); L10 = mp.log(10)
us = [l/2, 3*l/2, 5*l/2]
def J(O, w): return mp.quad(lambda v: 2/mp.sqrt(O+(1-O)*v**6), [w, 1])
def concl(O, b2, b3):
    A2 = L10*(mp.mpf(3)/2 - mp.mpf(3)/4*O); A3 = L10**2*(mp.mpf(9)/8*O**2 - 2*O + mp.mpf(7)/6)
    lhs = b2*L10 - A2 + mp.mpf(1)/2; rhs = mp.mpf(20)/3*(l/L10)*(b3*L10**2 - A3)
    return rhs - lhs   # > 0 means the conclusion holds
for O in [mp.mpf(x) for x in ['0', '0.3', '1']]:
    D = [(1+z)*J(O, 1/mp.sqrt(1+z)) for z in [mp.sqrt(2)-1, 2*mp.sqrt(2)-1, 4*mp.sqrt(2)-1]]
    for s in itertools.product([1, -1], repeat=3):
        # unknowns b2, b3, lam: u + b2 u^2 + b3 u^3 - lam s D = 0
        M = mp.matrix([[us[i]**2, us[i]**3, -s[i]*D[i]] for i in range(3)])
        rhs = mp.matrix([-us[i] for i in range(3)])
        b2, b3, lam = mp.lu_solve(M, rhs)
        print(float(O), s, 'lam', mp.nstr(lam, 5), 'conclusion margin', mp.nstr(concl(O, b2, b3), 5))
# Degenerate data: the dropped value is zero (Lean: logb of D/0 is logb 0 = 0, so that residual is |c| <= 1/20 and
# c = 0 works when H is chosen to make the two other ratios one), the two other values proportional to the distances.
print('zero value at one source')
for O in [mp.mpf(x) for x in ['0', '0.3', '1']]:
    D = [(1+z)*J(O, 1/mp.sqrt(1+z)) for z in [mp.sqrt(2)-1, 2*mp.sqrt(2)-1, 4*mp.sqrt(2)-1]]
    for k in range(3):
        rows = []; rhs = []
        for i in range(3):
            if i == k: rows.append([us[i]**2, us[i]**3, 0])
            else: rows.append([us[i]**2, us[i]**3, -D[i]])
            rhs.append(-us[i])
        b2, b3, lam = mp.lu_solve(mp.matrix(rows), mp.matrix(rhs))
        print(float(O), 'zero at source', k, 'lam', mp.nstr(lam, 5), 'conclusion margin', mp.nstr(concl(O, b2, b3), 5))
