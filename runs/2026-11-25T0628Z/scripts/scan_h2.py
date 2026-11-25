# Float scan: rl19_box_unmatched without Omega <= 1. Minimal magnitude spread over the box, per Omega > 1.
import mpmath as mp
mp.mp.dps = 30
l = mp.log10(2)
Z = [mp.sqrt(2)-1, 2*mp.sqrt(2)-1, 4*mp.sqrt(2)-1]
X = [l/2, 3*l/2, 5*l/2]
def chi(Om, z):
    return mp.quad(lambda y: 1/mp.sqrt(Om*(1+y)**3 + 1 - Om), [0, z])
def spread(Om, a2, a3):
    m = [5*mp.log10((1+z)*chi(Om, z)/(x + a2*x**2 + a3*x**3)) for z, x in zip(Z, X)]
    return max(m) - min(m), m
for Om in [1, 1.01, 1.1, 1.5, 2, 3, 5, 10, 20, 100, 1e3, 1e4, 1e6]:
    best = None
    for a2 in [3.43, 3.46, 3.49]:
        for a3 in [1.57, 1.63, 1.69]:
            s, m = spread(Om, a2, a3)
            if best is None or s < best[0]: best = (s, a2, a3, m)
    print(f"Om={Om}: min spread {float(best[0]):.4f} at a2={best[1]} a3={best[2]}; m1-m3={float(best[3][0]-best[3][1]):.4f} m5-m3={float(best[3][2]-best[3][1]):.4f}")
