# Second route (floating point, not evidence): scipy DOP853 from a series start, zero by event.
import numpy as np
from scipy.integrate import solve_ivp
n = 4.5
x0 = 1e-3
# series: theta = 1 - x^2/6 + n x^4/120 - ...
th0 = 1 - x0**2/6 + n*x0**4/120
ph0 = -x0/3 + n*x0**3/30
f = lambda x, y: [y[1], -2*y[1]/x - max(y[0], 0)**n]
ev = lambda x, y: y[0]; ev.terminal = True
s = solve_ivp(f, [x0, 40], [th0, ph0], method='DOP853', rtol=1e-14, atol=1e-16, events=ev)
z = s.t_events[0][0]; ph = s.y_events[0][0][1]
om = -z*z*ph
print('xi1', repr(z), 'omega', repr(om), 'conc', repr(z**3/(3*om)))
