"""Method A: scipy DOP853 in t = log s, state (w, y = s w'). Extrema of m where y^2 = 2 s^2 e^w (v = 2u)."""
import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import brentq

def rhs(t, Y):
    w, y = Y
    return [y, -y - np.exp(2*t + w)]

def m_of(t, Y):
    w, y = Y
    s = np.exp(t)
    return s*(-y)*np.exp(w/2)/np.sqrt(4*np.pi)  # s^2(-phi) e^{w/2}, phi = y/s

def g(t, Y):
    w, y = Y
    return y*y - 2*np.exp(2*t + w)

s0 = 1e-5
t0 = np.log(s0)
Y0 = [-s0**2/6 + s0**4/120, -s0**2/3 + s0**4/30]
for rtol in (1e-12, 1e-13, 3e-14):
    sol = solve_ivp(rhs, (t0, np.log(1e6)), Y0, method='DOP853', rtol=rtol, atol=1e-30,
                    dense_output=True, events=g)
    te = sol.t_events[0]
    print('rtol', rtol, 'nfev', sol.nfev)
    for t in te[:8]:
        t = brentq(lambda tt: g(tt, sol.sol(tt)), t-1e-6, t+1e-6, xtol=1e-15)
        Y = sol.sol(t)
        print('  xi=%.12f  m=%.12f  contrast=%.10e  4pi m^2=%.12f' % (np.exp(t), m_of(t, Y), np.exp(-Y[0]), 4*np.pi*m_of(t, Y)**2))
    print('  #extrema up to 1e6:', len(te))
    # sample mass curve
    ts = np.linspace(np.log(733), np.log(1e6), 200001)
    Ys = sol.sol(ts)
    ms = m_of(ts, Ys)
    print('  min m on [733,1e6] sample:', ms.min(), 'at xi', np.exp(ts[ms.argmin()]))
    print('  m(1e6)=', ms[-1], ' sqrt(2/pi)=', np.sqrt(2/np.pi))
    # inf of m over xi>=xi3, |xi-xi4|>=1
    xi = np.exp(ts)
    xi4 = np.exp(te[3])
    mask = np.abs(xi - xi4) >= 1
    print('  inf m over |xi-xi4|>=1 (sampled):', ms[mask].min(), 'gap vs m(xi4):', ms[mask].min() - ms.min())
    # homology at 20000
    t2 = np.log(20000.0)
    w, y = sol.sol(t2)
    v = -y; u = np.exp(2*t2 + w)/v
    V = (u - 1 - np.log(u)) + (v - 2 - 2*np.log(v/2))
    print('  at 20000: u=%.12f v=%.12f V=%.12e' % (u, v, V))
