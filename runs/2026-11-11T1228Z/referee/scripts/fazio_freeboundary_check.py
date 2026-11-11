"""Referee (run 2026-11-11T1228Z): at Fazio's printed wall shears (beta = -0.1988), where does the IVP first reach
f' = 1, and what is f'' there (a free-boundary truncation f'(eta_inf) = 1, f''(eta_inf) = eps would fix both)?
Usage: nice python3 fazio_freeboundary_check.py"""
from scipy.integrate import solve_ivp
beta = -0.1988
rhs = lambda t, y: [y[1], y[2], -y[0] * y[2] - beta * (1 - y[1] ** 2)]
ev = lambda t, y: y[1] - 1.0
ev.direction = 1
for alpha in [0.005221, -0.005158, 0.00521818788, -0.00515742018]:
    s = solve_ivp(rhs, (0, 40), [0, 0, alpha], method="DOP853", rtol=1e-13, atol=1e-16, events=ev)
    te = s.t_events[0]
    if len(te):
        print(f"alpha={alpha:+.11f}: f'=1 first at eta={te[0]:.6f}, f''there={s.y_events[0][0][2]:.4e}, f(eta)={s.y_events[0][0][0]:.6f}")
    else:
        print(f"alpha={alpha:+.11f}: no crossing on [0,40]")
