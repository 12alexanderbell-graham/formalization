# Independent derivation of H0 d_L(y) for curved FLRW, to y^5 (bracket to y^4).
import sympy as sp
q,j,s,l,k,tau,y,Om=sp.symbols('q j s l k tau y Omega0')
N=6
A = 1 + tau - q*tau**2/2 + j*tau**3/6 + s*tau**4/24 + l*tau**5/120   # a/a0, tau=H0(t-t0)
invA = sp.series(1/A, tau, 0, N).removeO()
# u = a0 H0 chi = int_tau^0 dtau'/A
u = -sp.integrate(invA, (tau,0,tau))
u = sp.expand(u)
F = u - k*u**3/6 + k**2*u**5/120          # a0 H0 S_K(chi), k = K/(a0H0)^2 = Omega0-1
dl = sp.series(invA*F, tau, 0, N+0).removeO()   # H0 d_L = (a0/a) a0 H0 S_K
yt = sp.series(1 - A, tau, 0, N).removeO()       # y = 1 - a/a0
# invert y(tau): tau = sum c_n y^n
cs = sp.symbols('c1:7')
tser = sum(cs[i]*y**(i+1) for i in range(N-1))
eq = sp.expand(sp.series(yt.subs(tau,tser), y, 0, N).removeO()) - y
sol={}
for n in range(1,N):
    co = sp.expand(eq.coeff(y,n)).subs(sol)
    c = cs[n-1]
    sol[c]=sp.solve(co,c)[0]
tser = tser.subs(sol)
dly = sp.expand(sp.series(dl.subs(tau,tser), y, 0, N).removeO())
D = [sp.factor(sp.expand(dly.coeff(y,n+1))) for n in range(5)]
for n in range(5): print('D%d ='%n, sp.expand(D[n]).subs(k,Om-1).expand())
P2 = -sp.Rational(1,6)*(12-5*q+3*q**2-j-Om)
P3 = sp.Rational(1,24)*(52-20*q+21*q**2-15*q**3-7*j+10*q*j+s-2*Om*(1+3*q))
P4 = sp.Rational(1,120)*(359-184*q+186*q**2-135*q**3+105*q**4+90*q*j-105*q**2*j-15*q*s-57*j+10*j**2+9*s-l-5*Om*(17-6*q+9*q**2-2*j))
Ds=[sp.expand(d.subs(k,Om-1)) for d in D]
print('D1 printed - correct:', sp.factor(-sp.Rational(1,2)*(-3+q)-Ds[1]))
print('D2 printed - correct:', sp.factor(sp.expand(P2-Ds[2])))
print('D3 printed - correct:', sp.factor(sp.expand(P3-Ds[3])))
print('D4 printed - correct:', sp.factor(sp.expand(P4-Ds[4])))
print('claimed D3 diff check:', sp.simplify(P3-Ds[3] + (Om-1)*(3*q-2)/6))
print('claimed D4 diff check:', sp.simplify(P4-Ds[4] + (Om-1)**2/120 + 5*q*(Om-1)/12))
import pickle; pickle.dump([str(x) for x in Ds], open('/home/claude/formalization/runs/2026-10-30T1028Z/referee/Ds.pkl','wb'))
# d_A = d_L (1-y)^2
dA = sp.expand(sp.series(dly*(1-y)**2, y,0,N).removeO())
DA=[sp.expand(dA.coeff(y,n+1).subs(k,Om-1)) for n in range(5)]
for n in range(5): print('DA%d ='%n, DA[n], '   x', sp.factor(DA[n]))
