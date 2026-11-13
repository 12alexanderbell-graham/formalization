"""Float cross-check of xi1, m1, m(7) with scipy DOP853 from a 4-term series at x=1e-3 (independent of mpmath odefun)."""
import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import brentq
x0 = 1e-3
p0 = x0**2/6 - x0**4/120 + x0**6/1890
dp0 = x0/3 - x0**3/30 + 6*x0**5/1890
f = lambda x, y: [y[1], np.exp(-y[0]) - 2*y[1]/x]
s = solve_ivp(f, (x0, 8), [p0, dp0], method='DOP853', rtol=1e-14, atol=1e-16, dense_output=True)
m = lambda x: (lambda y: x*x*y[1]*np.exp(-y[0]/2)/np.sqrt(4*np.pi))(s.sol(x))
g = lambda x: (lambda y: x*y[1] - 2*x*np.exp(-y[0])/y[1])(s.sol(x))
xi1 = brentq(g, 6, 7, xtol=1e-15)
print('xi1 =', repr(xi1), ' m1 =', repr(m(xi1)), ' m(7) =', repr(m(7.0)))
xs = np.linspace(x0, 8, 200001); ms = m(xs)
print('argmax on grid:', xs[ms.argmax()], ' monotone up to xi1:', np.all(np.diff(ms[xs<xi1])>0), ' down from xi1 to 8:', np.all(np.diff(ms[xs>xi1])<0))
