# C7 referee: independent derivation of H0 d_A(y) for general curvature, plus witness checks.
import sympy as sp
q,j,s,l,Om,tau,y,u,K=sp.symbols('q j s l Omega tau y u K')
N=6
# a0=1, H0=1  =>  Omega0-1 = K
a=1+tau-q*tau**2/2+j*tau**3/6+s*tau**4/24+l*tau**5/120
# chi = int_t^{t0} dt'/a = -int_0^tau du/a(u)
inv=sp.series(1/a.subs(tau,u),u,0,N).removeO()
chi=-sp.integrate(inv,(u,0,tau))
S=chi-K*chi**3/6+K**2*chi**5/120
dA=sp.expand(sp.series(a*S,tau,0,N+1).removeO())
# y = 1 - a(t)/a0 ; invert tau(y)
yexpr=sp.expand(1-a)
# series reversion via ansatz
b=sp.symbols('b1:7'); T=sum(b[i]*y**(i+1) for i in range(N))
ex=sp.expand(sp.series(yexpr.subs(tau,T),y,0,N+1).removeO())-y
sol={}
for k in range(1,N+1):
    ck=sp.expand(ex.coeff(y,k).subs(sol)); sol[b[k-1]]=sp.solve(ck,b[k-1])[0]
T=sp.expand(T.subs(sol))
dAy=sp.expand(sp.series(sp.expand(dA.subs(tau,T)),y,0,N).removeO())
dAy=dAy.subs(K,Om-1)
c=[sp.expand(dAy.coeff(y,k)) for k in range(N)]
print('c0,c1 =',c[0],c[1])
DA=[None,1,-(sp.Rational(1,2))*(1+q),-(sp.Rational(1,6))*(-q-3*q**2+j+Om)]
for k in (2,3): print('D%d check:'%(k-1),sp.simplify(c[k]-DA[k]))
pD3=-sp.Rational(1,24)*(-2*q+3*q**2+15*q**3-j-10*q*j-s+2*Om)
pD4=-sp.Rational(1,120)*(1-6*q+9*q**2-15*q**3-105*q**4+10*q*j+105*q**2*j+15*q*s-3*j-10*j**2+s+l+5*Om)
d3=sp.factor(pD3-c[4]); d4=sp.factor(pD4-c[5])
print('printed-correct D3 =',d3, ' claimed:',sp.simplify(d3-(-q*(Om-1)/4)))
print('printed-correct D4 =',d4, ' claimed:',sp.simplify(d4-(-(Om-1)*((Om-1)+10*j-45*q**2+20*q)/120)))
print('flat agreement:',sp.simplify(d3.subs(Om,1)),sp.simplify(d4.subs(Om,1)))
# witnesses: a=e^t K=1 t0=0 => H0=1,q=-1,j=s=l=1, Om=1+K/(H0^2 a0^2)=2
w={q:-1,j:1,s:1,l:1,Om:2}
print('exp K=1: dD3 =',d3.subs(w),' dD4 =',d4.subs(w))
# exact check of witness: d_A for a=e^t, K=1: chi = e^{-t}-1, y=1-e^t, d_A = e^t sin(e^{-t}-1)
t=sp.symbols('t')
yy=1-sp.exp(t); dAex=sp.exp(t)*sp.sin(sp.exp(-t)-1)
# t = log(1-y)
dAexy=sp.series(dAex.subs(t,sp.log(1-y)),y,0,6).removeO()
print('exact exp K=1 series:',sp.expand(dAexy))
print('formula at witness:',sp.expand(sum(c[k].subs(w)*y**k for k in range(6))))
# Milne a=t, K=-1, t0=1: q=j=s=l=0, Om=0 ; d_A = t sinh(log(1/t)) = (1-t^2)/2 ; y=1-t
wm={q:0,j:0,s:0,l:0,Om:0}
print('Milne formula:',sp.expand(sum(c[k].subs(wm)*y**k for k in range(6))),' exact: y - y^2/2 ; dD3,dD4 =',d3.subs(wm),d4.subs(wm))
