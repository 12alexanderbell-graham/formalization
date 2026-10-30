import sympy as sp
T,z,H,q,j,s,c,k=sp.symbols('T z H q j s c k')  # T = t0 - t >= 0 (lookback)
N=5
# a(t0 - T), a0=1
a = 1 - H*T - q/2*H**2*T**2 - j/6*H**3*T**3 + s/24*H**4*T**4   # (t-t0) = -T
zT = sp.series(1/a - 1, T, 0, N).removeO()
# invert z(T) -> T(z)
cs = sp.symbols('b1:%d'%N)
Tz = sum(cs[i]*z**(i+1) for i in range(N-1))
eq = sp.expand(sp.series(zT.subs(T,Tz), z, 0, N).removeO() - z)
sol = sp.solve([eq.coeff(z,i) for i in range(1,N)], cs, dict=True)[0]
Tz = sp.expand(Tz.subs(sol))
print("lookback H*T(z) =", sp.collect(sp.expand(H*Tz), z))
# chi(T) = c * int_0^T dT'/a(t0-T')
Tp=sp.symbols('Tp')
chiT = c*sp.integrate(sp.series(1/a.subs(T,Tp),Tp,0,N).removeO(), (Tp,0,T))
chiz = sp.series(chiT.subs(T,Tz), z, 0, N).removeO()
# r = sin(sqrt(k) chi)/sqrt(k) series: chi - k chi^3/6 + ...
r = chiz - k*chiz**3/6
dL = sp.series((1+z)*r, z, 0, N).removeO()
dL = sp.expand(dL*H/c)
for i in range(1,N):
    print(i, sp.factor(dL.coeff(z,i)))
# Visser's claimed
K = k*c**2/H**2
V = {1:1, 2:sp.Rational(1,2)*(1-q), 3:-sp.Rational(1,6)*(1-q-3*q**2+j+K), 4:sp.Rational(1,24)*(2-2*q-15*q**2-15*q**3+5*j+10*q*j+s+2*K*(1+3*q))}
for i in range(1,N):
    print("diff", i, sp.simplify(dL.coeff(z,i)-V[i]))
# Visser's D(z) = c * lookback
VD = z*(1-(1+q/2)*z+(1+q+q**2/2-j/6)*z**2-(1+sp.Rational(3,2)*q*(1+q)+sp.Rational(5,8)*q**3-j/2-sp.Rational(5,12)*q*j-s/24)*z**3)
print("lookback diff", sp.simplify(sp.expand(H*Tz-VD)))
