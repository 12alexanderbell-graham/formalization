# Attempt to reproduce CDL 2019 (261): f(z) = A + B z^2 e^{Cz}, (A,B,C) = (-5.024, 8.651, 0.512),
# from ODE (249) with H(z) to jerk order (246), Om=0.289, h=0.692, q0=-0.545, j0=0.776 (256),
# ICs (250) f_z(0)=1 and (251) f(0)=6H0^2(Om-2). H0 in units of 100 km/s/Mpc (h).
import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import curve_fit
Om, h, q, j = 0.289, 0.692, -0.545, 0.776
H = lambda z: h*(1 + (1+q)*z + (j-q**2)*z**2/2)
Hz = lambda z: h*((1+q) + (j-q**2)*z)
Hzz = lambda z: h*(j-q**2)
def rhs(z, y, form):
    f, fz = y
    R = (3*Hz(z) + (1+z)*Hzz(z))/Hz(z)
    R = R/H(z) if form == 'printed' else R*H(z)
    fzz = (R*fz - 3*f*Hz(z))/(H(z)*(1+z))
    return [fz, fzz]
zs = np.linspace(0, 2, 400)
model = lambda z, A, B, C: A + B*z**2*np.exp(C*z)
for form in ('printed', 'corrected'):
    for fz0, lab in ((1.0, 'fz(0)=1 (250)'), (-12*h**2*(1+q), 'fz(0)=T_z(0)')):
        sol = solve_ivp(rhs, (0, 2), [6*h**2*(Om-2), fz0], t_eval=zs, args=(form,), rtol=1e-10, atol=1e-12)
        try:
            p, _ = curve_fit(model, zs, sol.y[0], p0=(-5, 8, 0.5), maxfev=20000)
            res = sol.y[0] - model(zs, *p)
            R2 = 1 - np.sum(res**2)/np.sum((sol.y[0]-sol.y[0].mean())**2)
            print(f'{form:9s} {lab:16s} f(2)={sol.y[0][-1]:9.3f}  fit (A,B,C)=({p[0]:.3f}, {p[1]:.3f}, {p[2]:.3f})  R2={R2:.5f}')
        except Exception as e:
            print(form, lab, 'fit failed', e)

# (262): third-order H(z) with s0 = -0.192; (A,B,C) printed = (-5.022, 8.577, 0.532).
# Which sign of the z^3 term reproduces it: (246) as printed (+Q) or the correct one (-Q)?
s = -0.192
Q = -3*q**2*(1+q) + j*(3+4*q) + s
print('Q =', Q)
for sign, lab in ((+1, '(246) printed +Q'), (-1, 'correct -Q')):
    H = lambda z, sg=sign: h*(1 + (1+q)*z + (j-q**2)*z**2/2 + sg*Q*z**3/6)
    Hz = lambda z, sg=sign: h*((1+q) + (j-q**2)*z + sg*Q*z**2/2)
    Hzz = lambda z, sg=sign: h*((j-q**2) + sg*Q*z)
    sol = solve_ivp(rhs, (0, 2), [6*h**2*(Om-2), 1.0], t_eval=zs, args=('corrected',), rtol=1e-10, atol=1e-12)
    p, _ = curve_fit(model, zs, sol.y[0], p0=(-5, 8, 0.5), maxfev=20000)
    print(f'{lab:18s} fit (A,B,C)=({p[0]:.3f}, {p[1]:.3f}, {p[2]:.3f})')
