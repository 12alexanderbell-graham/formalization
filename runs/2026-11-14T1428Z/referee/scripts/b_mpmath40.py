"""Method B: mpmath Taylor integrator (odefun) at 30 digits, t = log s, state (w, y = s w').
Also Volterra bound in homology variables."""
import mpmath as mp
mp.mp.dps = 40

s0 = mp.mpf('1e-6'); t0 = mp.log(s0)
# series w = -s^2/6 + s^4/120 - s^6/1890
w0 = -s0**2/6 + s0**4/120 - s0**6/1890
y0 = -s0**2/3 + 4*s0**4/120 - 6*s0**6/1890
f = mp.odefun(lambda t, Y: [Y[1], -Y[1] - mp.exp(2*t + Y[0])], t0, [w0, y0])

def m_of(t):
    w, y = f(t)
    return mp.exp(t)*(-y)*mp.exp(w/2)/mp.sqrt(4*mp.pi)

def g(t):
    w, y = f(t)
    return y*y - 2*mp.exp(2*t + w)

out = {}
for name, guess in [('xi1', 6.4507514), ('xi2', 67.0075), ('xi3', 733.77), ('xi4', 7849.63)]:
    t = mp.findroot(g, mp.log(guess))
    w, y = f(t)
    out[name] = t
    print(name, mp.nstr(mp.exp(t), 20), 'm', mp.nstr(m_of(t), 20), 'contrast', mp.nstr(mp.exp(-w), 20))
t4 = out['xi4']
print('4 pi m(xi4)^2 =', mp.nstr(4*mp.pi*m_of(t4)**2, 20))
# m at xi4 +- 1
for d in (-1, 1):
    tt = mp.log(mp.exp(t4) + d)
    print('m(xi4%+d) - m(xi4) =' % d, mp.nstr(m_of(tt) - m_of(t4), 10))
# Volterra at 20000
t2 = mp.log(20000)
w, y = f(t2)
v = -y; u = mp.exp(2*t2 + w)/v
V0 = (u - 1 - mp.log(u)) + (v - 2 - 2*mp.log(v/2))
print('u(20000)=', mp.nstr(u, 20), 'v=', mp.nstr(v, 20), 'V=', mp.nstr(V0, 15))
print('m(20000)=', mp.nstr(m_of(t2), 15))
# min of u v^3 on {V <= V0}: Lagrange => v - 2 = 3(u - 1), u < 1 branch
def Vu(u):
    v = 2 + 3*(u - 1)
    return (u - 1 - mp.log(u)) + (v - 2 - 2*mp.log(v/2)) - V0
ustar = mp.findroot(Vu, mp.mpf('0.995'))
vstar = 2 + 3*(ustar - 1)
P = ustar*vstar**3
mm = 4*mp.pi*m_of(t4)**2
print('min u v^3 on sublevel =', mp.nstr(P, 20), ' at u,v=', mp.nstr(ustar, 15), mp.nstr(vstar, 15))
print('4pi m(xi4)^2 =', mp.nstr(mm, 20), ' margin =', mp.nstr(P - mm, 10))
print('equiv mass lower bound beyond 20000:', mp.nstr(mp.sqrt(P/(4*mp.pi)), 15), ' sqrt(2/pi)=', mp.nstr(mp.sqrt(2/mp.pi), 15))
