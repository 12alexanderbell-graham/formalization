"""Shape checks on the converged reversed solutions + independent cross-check with mpmath.odefun."""
from mpmath import mp, mpf, odefun, findroot
from referee_fs import step
mp.dps = 30
S = {'-0.15': '-0.1334212378952886965665', '-0.17': '-0.1142272390982548964906',
     '-0.18': '-0.09769206013457255614968', '-0.19': '-0.07133590600343803099647'}
for bs, ss in S.items():
    b = mpf(bs); y = (mpf(0), mpf(0), mpf(ss)); h = mpf(1)/16
    signs = []; pmax = mpf(-1); pmin = mpf(1); qprev = y[2]; eta = 0; zero_p = None
    for n in range(1, 16*16 + 1):
        y = step(y, b, h, 30)
        if y[2]*qprev < 0: signs.append(float(n*h))
        if zero_p is None and y[1] > 0: zero_p = float(n*h)
        qprev = y[2]; pmax = max(pmax, y[1]); pmin = min(pmin, y[1])
    print(bs, "f'' sign changes at eta~", signs, " f' becomes >0 at eta~", zero_p,
          " min f'=", mp.nstr(pmin, 8), " max(f'-1)=", mp.nstr(pmax - 1, 5), " f(16)-16=", mp.nstr(y[0] - 16, 10))
# cross-check with mpmath.odefun (independent Taylor integrator), beta=-0.17, Robin condition at L=12
mp.dps = 25
b = mpf('-0.17'); L = 12
def R(s):
    sol = odefun(lambda t, y: [y[1], y[2], -y[0]*y[2] - b*(1 - y[1]**2)], 0, [mpf(0), mpf(0), s])
    f, p, q = sol(L)
    return q - (1 - p)*(f + (1 + 2*b)/f)
print('odefun cross-check beta=-0.17, L=12:', mp.nstr(findroot(R, (mpf('-0.11422'), mpf('-0.11423')), solver='secant', tol=mpf(10)**-40), 20))
