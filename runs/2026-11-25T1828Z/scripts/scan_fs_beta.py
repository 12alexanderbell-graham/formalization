"""Run 2026-11-25T1828Z, for the next part-1 run: hypothesis 1 (beta < 0) of fs_neg_decay_equal, scanned on the dropped
region beta >= 0. For each beta, shoot f''' + f f'' + beta (1 - f'^2) = 0, f(0) = f'(0) = 0, f''(0) = s, and classify s:
'ok' if f'' stays positive and f' -> 1 (within 1e-6 by eta = 12), 'over' if f' exceeds 1, 'turn' if f'' vanishes with f' < 1.
Every class conclusion of the headline needs at most one 'ok' interval of width zero (a single s) per beta."""
import numpy as np
from scipy.integrate import solve_ivp
def classify(beta, s, T=14.0):
    def rhs(t, y): return [y[1], y[2], -y[0]*y[2] - beta*(1 - y[1]**2)]
    def over(t, y): return y[1] - 1.0
    over.terminal = True; over.direction = 1
    def turn(t, y): return y[2]
    turn.terminal = True; turn.direction = -1
    sol = solve_ivp(rhs, [0, T], [0, 0, s], events=[over, turn], rtol=1e-11, atol=1e-13)
    if sol.t_events[0].size: return 'over'
    if sol.t_events[1].size: return 'turn'
    return 'ok' if abs(sol.y[1, -1] - 1) < 1e-6 else 'short'
for beta in [0.0, 0.05, 0.1, 0.3, 0.5, 1.0, 1.5, 2.0, 5.0]:
    ss = np.linspace(0.01, 5.0, 2000)
    cls = [classify(beta, s) for s in ss]
    # boundaries between turn (too small) and over (too large)
    trans = [(ss[i], cls[i], cls[i+1]) for i in range(len(ss)-1) if cls[i] != cls[i+1]]
    print('beta=%.2f transitions:' % beta, ', '.join('%.4f %s->%s' % t for t in trans))
