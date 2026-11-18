# Independent high-precision computation of the turning points of lambda(s)=s^2 e^{W(s)},
# W'' + (2/s) W' + e^W = 0, W(0)=0, W'(0)=0.  Own Taylor-series integrator (mpmath).
import mpmath as mp
import sys
mp.mp.dps = int(sys.argv[1]) if len(sys.argv) > 1 else 40
NCEN = 80      # centre-series terms
S0 = mp.mpf('0.5')

def centre(s, N=NCEN):
    # w = sum a_k s^k, y = e^w = sum b_k s^k ; a_k = -b_{k-2}/(k(k+1)), k b_k = sum j a_j b_{k-j}
    a = [mp.mpf(0)]*(N+1); b = [mp.mpf(0)]*(N+1); b[0] = mp.mpf(1)
    for k in range(1, N+1):
        if k >= 2: a[k] = -b[k-2]/(k*(k+1))
        b[k] = mp.fsum(j*a[j]*b[k-j] for j in range(1, k+1))/k
    w = mp.fsum(a[k]*s**k for k in range(N+1))
    p = mp.fsum(k*a[k]*s**(k-1) for k in range(1, N+1))
    y = mp.fsum(b[k]*s**k for k in range(N+1))
    tail = abs(a[N]*s**N) + abs(a[N-1]*s**(N-1))
    return w, p, y, tail

def taylor_coeffs(s0, w0, p0, y0, N):
    w = [w0]+[0]*N; p = [p0]+[0]*N; y = [y0]+[0]*N
    for k in range(N):
        ym1 = y[k-1] if k >= 1 else 0
        p[k+1] = (-(k+2)*p[k] - s0*y[k] - ym1)/(s0*(k+1))
        y[k+1] = mp.fsum(y[j]*p[k-j] for j in range(k+1))/(k+1)
        w[k+1] = p[k]/(k+1)
    return w, p, y

def ev(c, h): return mp.polyval(c[::-1], h)

def integrate(s_end, h, N=30):
    s = S0; w, p, y, _ = centre(S0)
    traj = []
    while s < s_end:
        cw, cp, cy = taylor_coeffs(s, w, p, y, N)
        traj.append((s, cw, cp, cy))
        hh = min(h*s, s_end - s)
        w, p, y = ev(cw, hh), ev(cp, hh), ev(cy, hh)
        s = s + hh
    return traj

def state_at(traj, t):
    for (s, cw, cp, cy) in reversed(traj):
        if s <= t:
            hh = t - s
            return ev(cw, hh), ev(cp, hh), ev(cy, hh)

def turning_points(h, N=30, s_end=900):
    traj = integrate(s_end, h, N)
    g = lambda t: (lambda w,p,y: 2 + t*p)(*state_at(traj, t))
    zs = []; prev = None; t = S0
    grid = [S0*mp.mpf('1.01')**k for k in range(int(mp.log(s_end/S0)/mp.log(1.01)))]
    for i in range(len(grid)-1):
        if g(grid[i])*g(grid[i+1]) < 0:
            z = mp.findroot(g, (grid[i], grid[i+1]), solver='anderson')
            w, p, y = state_at(traj, z)
            zs.append((z, z*z*y, z*mp.e**w/(-p), -z*p))
        if len(zs) >= 3: break
    return zs

if __name__ == '__main__':
    w, p, y, tail = centre(S0)
    print('centre series tail at s0', mp.nstr(tail, 5), ' check y-e^w', mp.nstr(y-mp.e**w, 5))
    res = {}
    for h in [mp.mpf('0.2'), mp.mpf('0.1')]:
        res[h] = turning_points(h)
        print('h =', h)
        for i, (z, lam, u, v) in enumerate(res[h]):
            print(f'  zeta{i} = {mp.nstr(z, 30)}  lambda = {mp.nstr(lam, 30)}  u = {mp.nstr(u, 20)}  2u = {mp.nstr(2*u, 30)}')
    h1, h2 = list(res)
    print('step-halving differences:')
    for (a, b) in zip(res[h1], res[h2]):
        print('  dzeta', mp.nstr(abs(a[0]-b[0]), 3), ' dlambda', mp.nstr(abs(a[1]-b[1]), 3))
    z1, l1 = res[h2][1][:2]; z2, l2 = res[h2][2][:2]
    print('lam1 margins: lam1-1.664155 =', mp.nstr(l1 - mp.mpf('1.664155'), 6), ' 1.664157-lam1 =', mp.nstr(mp.mpf('1.664157') - l1, 6))
    print('lam2 margins: lam2-2.10852 =', mp.nstr(l2 - mp.mpf('2.10852'), 6), ' 2.10858-lam2 =', mp.nstr(mp.mpf('2.10858') - l2, 6))
    l0 = res[h2][0][1]
    print('lamStar margins:', mp.nstr(l0 - mp.mpf('3.321992118'), 6), mp.nstr(mp.mpf('3.321992119') - l0, 6))
