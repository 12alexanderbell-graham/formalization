# Float scan of the five B1 headlines for densities below 1/5 (hypothesis 1 = 1/5 <= Omega).
import mpmath as mp
mp.mp.dps = 30
L2 = mp.log(2); L10 = mp.log(10)
def J(O, lo):
    return mp.quad(lambda v: 2/mp.sqrt(O+(1-O)*v**6), [lo, 1])
def Qc(O, u):
    return u + (mp.mpf(3)/2 - mp.mpf(3)/4*O)*u**2 + (mp.mpf(9)/8*O**2 - 2*O + mp.mpf(7)/6)*u**3
def lusA2(O): return L10*(mp.mpf(3)/2 - mp.mpf(3)/4*O)
def lusA3(O): return L10**2*(mp.mpf(9)/8*O**2 - 2*O + mp.mpf(7)/6)
x3 = 2*L2/L10; x7 = 3*L2/L10
def sep(O, J3, J7):
    r = 2*J7/J3  # DL7/DL3
    A2, A3 = lusA2(O), lusA3(O)
    best = None; side_ok = True
    for k in [mp.mpf(-1), mp.mpf(1)]:
        R = r*mp.power(10, k*mp.mpf('0.02'))
        # line: x7 + a2 x7^2 + a3 x7^3 - R (x3 + a2 x3^2 + a3 x3^3) = 0
        c0 = x7 - R*x3; c2 = x7**2 - R*x3**2; c3 = x7**3 - R*x3**3
        f = c0 + c2*A2 + c3*A3
        d = abs(f)/mp.sqrt(c2**2+c3**2)
        best = d if best is None else min(best, d)
    # point inside band? check sign change
    vals = []
    for k in [-1, 1]:
        R = r*mp.power(10, k*mp.mpf('0.02'))
        vals.append(x7 - R*x3 + (x7**2 - R*x3**2)*A2 + (x7**3 - R*x3**3)*A3)
    inside = vals[0]*vals[1] <= 0
    return (0 if inside else best)
for O in [mp.mpf(x) for x in ['-0.0019','-0.001','0','0.02','0.05','0.1','0.15','0.2']]:
    J3 = J(O, mp.mpf(1)/2); J7 = J(O, 1/mp.sqrt(8))
    m3 = 5*mp.log10(4*J3/Qc(O, 2*L2)); m7 = 5*mp.log10(8*J7/Qc(O, 3*L2))
    print(float(O), 'm3', float(m3), 'm7', float(m7), 'shape', float(m7-m3), 'sepdist', float(sep(O,J3,J7)))
