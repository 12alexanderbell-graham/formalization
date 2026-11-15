"""Method B: scipy DOP853 on (w, phi) with independent variable t = log(xi).
dw/dt = xi*phi, dphi/dt = -2 phi - xi e^w. Extrema of m: zeros of g = phi^2 - 2 e^w (<=> 2u = v).
Also integrate homology variables (u,v) in t with DOP853 as a cross-check."""
import numpy as np
from scipy.integrate import solve_ivp

def series(x):
    # w = -x^2/6 + x^4/120 - x^6/1890 + 61 x^8/1632960
    w = -x**2/6 + x**4/120 - x**6/1890 + 61*x**8/1632960
    p = -x/3 + x**3/30 - 6*x**5/1890 + 8*61*x**7/1632960
    return w, p

def rhs(t, y):
    x = np.exp(t); w, p = y
    return [x*p, -2*p - x*np.exp(w)]

def g(t, y):
    return y[1]**2 - 2*np.exp(y[0])

def mass(x, w, p):
    return x**2*(-p)*np.exp(w/2)/np.sqrt(4*np.pi)

x0 = 1e-3
w0, p0 = series(x0)
T1 = np.log(3e8)
sol = solve_ivp(rhs, [np.log(x0), T1], [w0, p0], method='DOP853', rtol=1e-13, atol=1e-15,
                events=g, dense_output=True)
print("method B (w,phi in t):")
for te, ye in zip(sol.t_events[0], sol.y_events[0]):
    x = np.exp(te)
    print(f"  xi = {x:.12g}   m = {mass(x, *ye):.15f}")
print("  sqrt(2/pi) =", np.sqrt(2/np.pi))

# homology variables
def rhs_uv(t, y):
    u, v = y
    return [u*(3-u-v), v*(u-1)]
def g2(t, y):
    return 2*y[0]-y[1]
u0 = x0*np.exp(w0)/(-p0); v0 = -x0*p0
sol2 = solve_ivp(rhs_uv, [np.log(x0), T1], [u0, v0], method='DOP853', rtol=1e-13, atol=1e-16,
                 events=g2, dense_output=True)
print("method B' (u,v in t):")
for te, ye in zip(sol2.t_events[0], sol2.y_events[0]):
    u, v = ye
    print(f"  xi = {np.exp(te):.12g}   m = {np.sqrt(u*v**3/(4*np.pi)):.15f}   u = {u:.12f}")
u, v = sol2.sol(np.log(3e5))
e1, e2 = u-1, v-2
print("N at xi=3e5:", 7*e1**2 + (e1+2*e2)**2, "sqrtN", np.sqrt(7*e1**2 + (e1+2*e2)**2), "u,v", u, v)
