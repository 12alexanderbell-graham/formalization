# Method 1: integrate w'' + (2/s) w' + e^w = 0 in the radius s (scipy DOP853),
# sample g(s) = 2 e^w - phi^2 densely (sign(dm/ds) = sign(g), since
# dm/ds = s^2 (e^w - phi^2/2) e^{w/2} / sqrt(4 pi)), and locate the sign changes.
import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import brentq

C = np.sqrt(4*np.pi)
s0 = 1e-3
# series: w = -s^2/6 + s^4/120 - s^6/1890, phi = w'
w0 = -s0**2/6 + s0**4/120 - s0**6/1890
p0 = -s0/3 + s0**3/30 - 6*s0**5/1890

def f(s, y):
    w, p = y
    return [p, -2*p/s - np.exp(w)]

S_END = 3.0e6
sol = solve_ivp(f, [s0, S_END], [w0, p0], method='DOP853', rtol=1e-13, atol=1e-16, dense_output=True)
print('status', sol.status, sol.message)

def g(s):
    w, p = sol.sol(s)
    return 2*np.exp(w) - p*p

def m(s):
    w, p = sol.sol(s)
    return s*s*(-p)*np.exp(w/2)/C

# [0, s0]: series m'(s) sign: g(s) = 2 e^w - phi^2 = 2 - O(s^2) > 0; check explicitly
ss = np.linspace(0, s0, 50)
gs = 2*np.exp(-ss**2/6) - (ss/3)**2
print('g on [0,1e-3] min', gs.min())

# dense geometric grid
grid = np.unique(np.concatenate([np.linspace(s0, 100, 2_000_001), np.geomspace(100, S_END, 4_000_001)]))
G = g(grid)
idx = np.where(np.sign(G[:-1]) != np.sign(G[1:]))[0]
zeros = [brentq(g, grid[i], grid[i+1], xtol=1e-14, rtol=1e-15) for i in idx]
print('number of sign changes of g on [1e-3, %.1e]:' % S_END, len(zeros))
L = np.sqrt(2/np.pi)
for k, z in enumerate(zeros):
    kind = 'max' if k % 2 == 0 else 'min'
    # check sign pattern of g just before and after
    print(f'k={k} {kind} xi={z:.10g}  m={m(z):.12f}  m-sqrt(2/pi)={m(z)-L:+.3e}')
# consistency: before zero 0 g>0, alternates
print('g(first grid pt) > 0:', G[0] > 0)
# min |g| scaled away from zeros: report min |g|*s^2 e^{-w}... (relative) on each segment
for k in range(len(zeros)-1):
    a, b = zeros[k], zeros[k+1]
    mask = (grid > a + 1e-3*(b-a)) & (grid < b - 1e-3*(b-a))
    print(f'segment {k}-{k+1}: sign g = {np.sign(G[mask]).min():+.0f}..{np.sign(G[mask]).max():+.0f}, points {mask.sum()}')
