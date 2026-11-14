"""Float study (run 2026-11-14T1028Z, unchecked): does a weighted one-sided (logarithmic-norm) cell keep the
Bonnor–Ebert homology enclosure bounded? Trajectory in t = log s: u' = u(3 - u - v), v' = v(u - 1), from s = 7.
Reports: growth of the fundamental matrix (true error amplification), and the logarithmic norm mu_W(J) of the
Jacobian in the weighted norm |W x|_2 with W from the real Jordan basis at the focus (1, 2)."""
import numpy as np, math
from scipy.integrate import solve_ivp
J0 = np.array([[-1., -1.], [2., 0.]])
ev, P = np.linalg.eig(J0)
Q = np.column_stack([P[:, 0].real, P[:, 0].imag])  # real Jordan basis
W = np.linalg.inv(Q)
def jac(u, v): return np.array([[3 - 2*u - v, -u], [v, u - 1]])
def mu(A):  # log norm in |W x|_2
    B = W @ A @ np.linalg.inv(W); return max(np.linalg.eigvalsh((B + B.T) / 2))
def mu2(A): return max(np.linalg.eigvalsh((A + A.T) / 2))
def f(t, y):
    u, v = y[0], y[1]; Phi = y[2:].reshape(2, 2)
    return np.concatenate([[u*(3-u-v), v*(u-1)], (jac(u, v) @ Phi).ravel()])
u7, v7 = 1.155239948201474, 2.471741654165   # state at s = 7 (BEHChain start, centre)
sol = solve_ivp(f, [math.log(7), math.log(1e5)], [u7, v7, 1, 0, 0, 1], rtol=1e-11, atol=1e-13, dense_output=True)
cum_w = 0.0; cum_2 = 0.0; prev = math.log(7); worst = -9
for s in [10, 20, 50, 150, 734, 2000, 7850, 2e4, 1e5]:
    t = math.log(s)
    ts = np.linspace(prev, t, 400)
    for a, b in zip(ts[:-1], ts[1:]):
        y = sol.sol((a + b) / 2); m = mu(jac(y[0], y[1])); worst = max(worst, m) if s > 50 else worst
        cum_w += m * (b - a); cum_2 += mu2(jac(y[0], y[1])) * (b - a)
    prev = t
    y = sol.sol(t); Phi = y[2:].reshape(2, 2)
    print('s=%-8g |Phi|_2=%.3g  |Phi|_W=%.3g  exp(int mu_W)=%.3g  exp(int mu_2)=%.3g' % (
        s, np.linalg.norm(Phi, 2), np.linalg.norm(W @ Phi @ np.linalg.inv(W), 2), math.exp(cum_w), math.exp(cum_2)))
print('max mu_W along the trajectory for s > 50:', worst)
