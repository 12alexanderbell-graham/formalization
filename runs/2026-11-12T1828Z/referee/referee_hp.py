"""dps=60 recompute (Robin, L=16) to show the f''(eta~14) sign change / f'>1 at the 1e-23 level is a precision artifact."""
import sys
from mpmath import mp, mpf
from referee_fs import step, secant
mp.dps = 60
for bs in sys.argv[1:]:
    b = mpf(bs); g = {'-0.15': mpf('-0.13342123789528869657'), '-0.18': mpf('-0.097692060134572556150')}[bs]
    s = secant(g, g + mpf('1e-20'), b, 16, mpf(1)/16, 40, 'B', mpf(10)**-55)
    y = (mpf(0), mpf(0), s); qprev = s; ch = []; pmax = mpf(-1)
    for n in range(1, 257):
        y = step(y, b, mpf(1)/16, 40)
        if y[2]*qprev < 0: ch.append(n/16)
        qprev = y[2]; pmax = max(pmax, y[1])
    print(bs, 's=', mp.nstr(s, 30), "f'' sign changes", ch, "max(f'-1)=", mp.nstr(pmax - 1, 5), flush=True)
