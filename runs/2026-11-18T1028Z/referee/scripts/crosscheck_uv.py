# Cross-check in homology variables (t = ln s): u' = u(3-u-v), v' = v(u-1); turning points v=2, lambda = u v.
import numpy as np, mpmath as mp, sys
from scipy.integrate import solve_ivp
sys.path.insert(0, '.')
from turning import centre
mp.mp.dps = 30
s0 = mp.mpf('0.5'); w, p, y, _ = centre(s0)
u0 = float(s0*y/(-p)); v0 = float(-s0*p)
f = lambda t, z: [z[0]*(3-z[0]-z[1]), z[1]*(z[0]-1)]
ev = lambda t, z: z[1]-2
sol = solve_ivp(f, [np.log(0.5), np.log(900)], [u0, v0], method='DOP853', rtol=1e-13, atol=1e-15, events=ev)
for t, z in zip(sol.t_events[0], sol.y_events[0]):
    print(f'zeta = {np.exp(t):.12f}  u = {z[0]:.15f}  lambda = 2u = {2*z[0]:.13f}  u-1 = {z[0]-1:+.3f}')
