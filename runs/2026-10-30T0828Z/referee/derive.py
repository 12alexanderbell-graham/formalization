import sympy as sp
T,H,c,a0,K,q,j,s,z,y,Om = sp.symbols('T H c a0 K q j s z y Omega0')
N=5
# a(t0-T)/a0 using definitions (10.1)-(10.4): a'=Ha, a''=-qH^2 a, a'''=jH^3 a, a''''=sH^4 a
ratio = 1 - H*T - q*H**2*T**2/2 - j*H**3*T**3/6 + s*H**4*T**4/24
onepz = sp.series(1/ratio, T, 0, N).removeO()   # 1+z = a0/a(t)
# chi = int_{t0-T}^{t0} c dt / a(t) = int_0^T c dT'/(a0*ratio(T'))
Tp=sp.symbols('Tp')
chi = sp.integrate(sp.series(c/(a0*ratio.subs(T,Tp)),Tp,0,N).removeO(),(Tp,0,T))
# r0 = S_K(chi), K=+1 sin, 0 identity, -1 sinh ; generic: chi - K chi^3/6 + K^2 chi^5/120
r0 = chi - K*chi**3/6 + K**2*chi**5/120
dL = sp.expand(sp.series(onepz*a0*r0, T, 0, N+1).removeO())
# invert z(T)
zT = sp.expand(onepz-1)
# T as series in z
Tz = sum(sp.Symbol('b%d'%i)*z**i for i in range(1,N+1))
eqs = sp.expand(sp.series(zT.subs(T,Tz),z,0,N+1).removeO()) - z
sol = sp.solve([eqs.coeff(z,i) for i in range(1,N+1)], [sp.Symbol('b%d'%i) for i in range(1,N+1)], dict=True)[0]
Tz = Tz.subs(sol)
dLz = sp.series(dL.subs(T,Tz), z, 0, N).removeO()
# K -> Omega0: K c^2/(H^2 a0^2) = Om-1  => K = (Om-1) H^2 a0^2 / c^2
dLz = sp.expand(dLz.subs(K,(Om-1)*H**2*a0**2/c**2))
print("z-series coefficients D^i_L (d_L = cz/H [sum D^i z^i]):")
for i in range(1,N):
    print(i-1, sp.factor(sp.simplify(dLz.coeff(z,i)*H/c)))
dLy = sp.series(dLz.subs(z, y/(1-y)), y, 0, N).removeO()
print("y-series coefficients D^i_{L,y}:")
Dy=[]
for i in range(1,N):
    co=sp.expand(sp.simplify(dLy.coeff(y,i)*H/c)); Dy.append(co)
    print(i-1, co, "   *6 =", sp.expand(6*co) if i==3 else "")
printed = -sp.Rational(1,6)*(12-5*q+3*q**2-j-Om)
print("D2 - printed(10.54):", sp.simplify(Dy[2]-printed))
print("D2 - (+)(10.54):", sp.simplify(Dy[2]+printed))
print("D1 - printed(10.53):", sp.simplify(Dy[1]-(-sp.Rational(1,2)*(-3+q))))
# d_A = d_L/(1+z)^2 = d_L (1-y)^2
dAy = sp.expand(sp.series(dLy*(1-y)**2, y,0,N).removeO())
print("d_A y-series coeffs:")
for i in range(1,N): print(i-1, sp.expand(dAy.coeff(y,i)*H/c))
print("d_A z-series coeffs:")
dAz = sp.expand(sp.series(dLz/(1+z)**2,z,0,N).removeO())
for i in range(1,N): print(i-1, sp.expand(dAz.coeff(z,i)*H/c))
# de Sitter check
print("deSitter D_y:", [sp.simplify(d.subs({q:-1,j:1,s:1,Om:1})) for d in Dy])
