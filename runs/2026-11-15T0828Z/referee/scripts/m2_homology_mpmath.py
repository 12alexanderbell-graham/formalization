# Method 2: Milne homology variables u = xi e^w/(-w'), v = -xi w', t = ln xi:
#   du/dt = u(3 - u - v),  dv/dt = v(u - 1),  u v^3 = 4 pi m^2,
#   d ln(m^2)/dt = 2u - v.
# Integrate with mpmath's Taylor-series ODE solver (30 digits), sample h = 2u - v
# on a dense t-grid, find zeros with findroot, check simplicity (dh/dt != 0) and
# that h > 0 on (0, xi_0] (u -> 3, v -> 0 as xi -> 0, so h -> 6).
import mpmath as mp
mp.mp.dps = 30

x0 = mp.mpf('1e-4')
w0 = -x0**2/6 + x0**4/120 - x0**6/1890
p0 = -x0/3 + x0**3/30 - 6*x0**5/1890
u0 = x0*mp.e**w0/(-p0)
v0 = -x0*p0
t0 = mp.log(x0)
F = lambda t, y: [y[0]*(3 - y[0] - y[1]), y[1]*(y[0] - 1)]
sol = mp.odefun(F, t0, [u0, v0], tol=mp.mpf(10)**(-25), degree=30)
h = lambda t: (lambda y: 2*y[0] - y[1])(sol(t))
dh = lambda t: (lambda y: 2*y[0]*(3 - y[0] - y[1]) - y[1]*(y[0] - 1))(sol(t))

T_END = mp.log(mp.mpf('3e6'))
N = 6000
ts = [t0 + (T_END - t0)*i/N for i in range(N + 1)]
hs = [h(t) for t in ts]
print('h at xi=1e-4:', mp.nstr(hs[0], 12))
zeros = []
for i in range(N):
    if mp.sign(hs[i]) != mp.sign(hs[i+1]):
        z = mp.findroot(h, (ts[i], ts[i+1]), solver='anderson')
        zeros.append(z)
print('sign changes of 2u-v for xi in [1e-4, 3e6]:', len(zeros))
L = mp.sqrt(2/mp.pi)
for k, z in enumerate(zeros):
    u, v = sol(z)
    m = mp.sqrt(u*v**3/(4*mp.pi))
    print(f"k={k} xi={mp.nstr(mp.e**z, 15)} m={mp.nstr(m, 15)} m-L={mp.nstr(m-L, 6)} d(2u-v)/dt={mp.nstr(dh(z), 6)}")
# minimum |h| on grid points between zeros, normalised by local max |h| (no near-tangency)
segs = [t0] + zeros + [T_END]
for j in range(len(segs) - 1):
    a, b = segs[j], segs[j+1]
    inner = [abs(hs[i]) for i in range(N+1) if a + (b-a)*mp.mpf('0.05') < ts[i] < b - (b-a)*mp.mpf('0.05')]
    sg = set(int(mp.sign(hs[i])) for i in range(N+1) if a < ts[i] < b)
    if inner:
        print(f'segment {j}: signs {sg}, min|h| on inner 90% = {mp.nstr(min(inner), 6)}')
