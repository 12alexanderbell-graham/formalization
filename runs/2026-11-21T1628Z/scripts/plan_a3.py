# Certificate plan (exact rationals) for: every matching cubic has e3 >= (tau - A3(Om))*m + delta on [0,1].
# Fresh tangent lower certs L1, L5 (at the cell midpoint) and chord upper certs U1, U3 on each cell.
import sys
from gen_fit import *
TAU = F(sys.argv[1]) if (len(sys.argv) > 1 and __name__ == "__main__") else F(491, 1000)
N = int(sys.argv[2]) if (len(sys.argv) > 2 and __name__ == "__main__") else 20
MM = F(333, 1000); DEL = F(1, 1000)
PAIRS = [[(3,1),(3,5)], [(1,5),(3,5)], [(3,1),(1,5)]]
def A3p(): return [F(7,6), F(-2), F(9,8)]
def target(): # (tau - A3)*MM + DEL as poly
    return padd([TAU*MM + DEL, F(0), F(0)], pscale(A3p(), -MM))
def lin_eval(p, O, w): return p[0] + p[1]*O + p[2]*w
def try_pair(a, b, pr, low, upp):
    cons = []
    for (k, j) in pr:
        r = R[(k, j)]; Lc = low[j]; Uc = upp[k]
        Lv = lambda O: Lc['A_'] - Lc['B_']*O; Uv = lambda O: Uc['C_'] + Uc['D_']*O
        if min(Lv(a), Lv(b)) <= 0: return None
        rho = rat(float(max(r*Uv(O)/(KAPPA*Lv(O)) for O in (a, b))), 6, up=True)
        while any(rho*KAPPA*Lv(O) < r*Uv(O) for O in (a, b)): rho += F(1, 10**6)
        cons.append((k, j, rho))
    (k1, j1, r1), (k2, j2, r2) = cons
    a11 = F(k1**2 - r1*j1**2, 4); a12 = F(k2**2 - r2*j2**2, 4)
    a21 = F(k1**3, 8) - r1*F(j1**3, 8); a22 = F(k2**3, 8) - r2*F(j2**3, 8)
    a11 = F(k1**2,4) - r1*F(j1**2,4); a12 = F(k2**2,4) - r2*F(j2**2,4)
    det = a11*a22 - a12*a21
    if det == 0: return None
    # l1*a11 + l2*a12 = 0 ; l1*a21 + l2*a22 = -1
    l1 = (0*a22 - a12*(-1))/det; l2 = (a11*(-1) - a21*0)/det
    if l1 < 0 or l2 < 0: return None
    S = [F(0)]*3
    for (k, j, rho), lam in zip(cons, (l1, l2)):
        S = padd(S, pscale(padd(Qlo(k), pscale(Qhi(j), rho), -1), lam))
    E = padd(S, target(), -1)
    verts = [(a, a*a), (b, b*b), ((a+b)/2, a*b)]
    mn = min(lin_eval(E, O, w) for O, w in verts)
    return dict(a=a, b=b, cons=cons, lam=(l1, l2), S=S, min=mn, ok=mn > 0)
def certs(a, b):
    mid = (a+b)/2
    low = {j: lower_cert(j, mid, N) for j in (1, 5)}
    upp = {k: upper_cert(k, a, b, N) for k in (1, 3)}
    for c in low.values(): c['A_'], c['B_'] = lower_trunc(c)
    for c in upp.values(): c['C_'], c['D_'] = upper_round(c)
    return low, upp
def solve(a, b, depth=0):
    low, upp = certs(a, b)
    best = None
    for pr in PAIRS:
        r = try_pair(a, b, pr, low, upp)
        if r and (best is None or r['min'] > best['min']): best = r
    if best and best['ok']: return [(best, low, upp)]
    if depth > 8: raise SystemExit(f'fail at [{float(a)},{float(b)}] best {best and float(best["min"])}')
    m = (a+b)/2
    return solve(a, m, depth+1) + solve(m, b, depth+1)
if __name__ == '__main__':
    res = solve(F(0), F(1))
    print(len(res), 'cells', [(float(r[0]['a']), float(r[0]['b']), r[0]['cons'][0][:2], r[0]['cons'][1][:2], float(r[0]['min'])) for r in res])
