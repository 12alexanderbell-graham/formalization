# Thomas-Fermi shooting in t = sqrt(x): Y' = 2 t P, P' = 2 Y^{3/2}, Y(0)=1, P(0)=s.
import mpmath as mp
mp.mp.dps = 40
B = mp.mpf('-1.588071022611375312718684508')
def run(s, tmax=12, h=mp.mpf(1)/256):
    # Taylor integration by mpmath odefun
    f = mp.odefun(lambda t, v: [2*t*v[1], 2*mp.power(v[0], 1.5) if v[0] > 0 else mp.mpf(0)], 0, [mp.mpf(1), s])
    t = mp.mpf(0)
    while t < tmax:
        t += mp.mpf(1)/4
        Y, P = f(t)
        if Y <= 0: return ('zero', t, Y, P)
        if P >= 0: return ('up', t, Y, P)
    return ('none', t, Y, P)
import sys
for d in [mp.mpf('1e-6'), mp.mpf('1e-9'), mp.mpf('1e-12')]:
    print(d, run(B - d), run(B + d))
