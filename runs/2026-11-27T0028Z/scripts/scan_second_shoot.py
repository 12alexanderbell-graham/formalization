#!/usr/bin/env python3
"""Run 2026-11-27T0028Z (float scan, not evidence): the second shooting window for the overshoot-and-return
zero-shear solution near beta = -2.4145 (witness candidate for the positivity hypotheses). Events after the first
return of p below one (time eta_r): Over2 = p > 1 again later; Slow2 = p < 1 from eta_r on with the slow sign
(q < 3(1 - p), as the separation stack's slow event) at some later time; and the sign of q along the way."""
import numpy as np
from scipy.integrate import solve_ivp
def run(b, L=12):
    rhs = lambda t, y: [y[1], y[2], -y[0]*y[2] - b*(1 - y[1]**2)]
    return solve_ivp(rhs, [0, L], [0, 0, 0], max_step=0.002, rtol=1e-12, atol=1e-14)
def classify(b):
    s = run(b); t, (f, p, q) = s.t, s.y
    i1 = np.argmax(p > 1); ir = i1 + np.argmax(p[i1:] < 1)  # first overshoot, first return
    after = p[ir:]
    over2 = np.any(after > 1)
    j = ir + np.argmax(after > 1) if over2 else len(t) - 1
    return dict(beta=b, t_over=t[i1], t_ret=t[ir], f_ret=f[ir], p_ret=p[ir], q_ret=q[ir], over2=bool(over2),
                t_end=t[j], minp_after=after.min(), q_end=q[-1], p_end=p[-1])
bs = -2.4145017520
for d in (-2e-2, -1e-2, -3e-3, -1e-3, 0, 1e-3, 3e-3, 1e-2, 2e-2):
    r = classify(bs + d)
    print(' '.join(f'{k}={v:+.5f}' if isinstance(v, float) else f'{k}={v}' for k, v in r.items()))
