import numpy as np
from scipy.integrate import solve_ivp

S = {-0.13: 0.26142275598711485691, -0.14: 0.23973595531176542349, -0.16: 0.19077985526867043498}

def shoot(beta, s, T=300.0):
    def ode(x, y):
        return [y[1], y[2], -y[0] * y[2] - beta * (1 - y[1] ** 2)]
    def ev_q(x, y): return y[2]
    ev_q.terminal = True; ev_q.direction = -1
    def ev_p(x, y): return y[1] - 1.5
    ev_p.terminal = True
    sol = solve_ivp(ode, (0, T), [0, 0, s], method='DOP853', rtol=1e-13, atol=1e-16,
                    events=[ev_q, ev_p], dense_output=True)
    return sol

for beta, ss in S.items():
    print('beta', beta, 's*', ss)
    for s in [1e-4, 0.01, 0.05, 0.1, ss * 0.5, ss - 1e-2, ss - 1e-3, ss - 1e-6, ss - 1e-9,
              ss + 1e-9, ss + 1e-6, ss + 1e-3, ss + 0.1, 1.0, 5.0]:
        sol = shoot(beta, s)
        xe = sol.t[-1]
        y = sol.y[:, -1]
        info = ''
        if sol.t_events[0].size:
            info = f'q=0 at eta={sol.t_events[0][0]:.3f}, p there={sol.y_events[0][0][1]:.6f}'
        elif sol.t_events[1].size:
            info = f'p hit 1.5 at {sol.t_events[1][0]:.3f}'
        else:
            # check positivity of q along trajectory and ratio
            xs = np.linspace(0, xe, 20001)
            Y = sol.sol(xs)
            ratios = [(e, sol.sol(e)[2] / (1 - sol.sol(e)[1])) for e in (50.0, 100.0, 200.0, 300.0)]
            info = (f'min q={Y[2].min():.3e}, max p={Y[1].max():.12f}, 1-p(300)={1 - y[1]:.3e}, '
                    + ' '.join(f'q/(1-p)@{e:.0f}={r:.4e}' for e, r in ratios)
                    + f'  (-2b/eta@300={-2 * beta / (300 - 0):.3e})')
        print(f'  s={s:.12g}: end={xe:.2f} {info}')
