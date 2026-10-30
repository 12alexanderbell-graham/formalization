from sympy import *
t,s,t0,R,c,h,n,tau=symbols('t s t0 R c h n tau',real=True)
def S(K,x):
    if K==0: return x
    return sin(sqrt(K)*x)/sqrt(K) if K>0 else sinh(sqrt(-K)*x)/sqrt(-K)
def chi(a,T0,T): return integrate(1/a(s),(s,T,T0))
def dM(K,a,T0,T): return a(T0)*S(K,chi(a,T0,T))
def dL(K,a,T0,T): return dM(K,a,T0,T)*a(T0)/a(T)
def dA(K,a,T0,T): return dM(K,a,T0,T)*a(T)/a(T0)
tp=symbols('tp',positive=True)
res={}
res['L deSitter']=simplify(dL(0,exp,0,t)-(exp(-t)-1)*exp(-t))
res['L milne']=simplify((dL(-1,lambda x:x,1,tp)-((1/tp)**2-1)/2).rewrite(exp))
res['L staticClosed']=simplify(dL(1,lambda x:1,t0,t)-sin(t0-t))
res['A deSitter']=simplify(dA(0,exp,0,t)-(1-exp(t)))
res['A deSitterContr']=simplify(dA(0,lambda x:exp(-x),0,t)-(exp(-t)-1))
res['A milne']=simplify((dA(-1,lambda x:x,1,tp)-(1-tp**2)/2).rewrite(exp))
Rp=symbols('Rp',positive=True)
res['A staticClosed']=simplify(dA(1,lambda x:Rp,t0,t)-Rp*sin((t0-t)/Rp))
res['A staticFlat']=simplify(dA(0,lambda x:Rp,t0,t)-(t0-t))
# Etherington consistency LumDistSpec vs AngDistSpec anchors
res['Eth deSitter']=simplify((1-exp(t))*exp(-2*t)-(exp(-t)-1)*exp(-t))
res['Eth milne']=simplify((1-tp**2)/2/tp**2-((1/tp)**2-1)/2)
# rescale: K->c^2 K, a->c a for K=+-1 symbolic chi
cp,chi_,Kp=symbols('cp chi Kp',positive=True)
res['rescale K>0']=simplify(cp*sin(sqrt(cp**2*Kp)*chi_/cp)/sqrt(cp**2*Kp)-sin(sqrt(Kp)*chi_)/sqrt(Kp))
res['rescale K<0']=simplify(cp*sinh(sqrt(cp**2*Kp)*chi_/cp)/sqrt(cp**2*Kp)-sinh(sqrt(Kp)*chi_)/sqrt(Kp))
H=lambda a,T: (diff(a(s),s)/a(s)).subs(s,T)
q=lambda a,T: (-diff(a(s),s,2)*a(s)/diff(a(s),s)**2).subs(s,T)
res['H powerLaw']=simplify(H(lambda x:x**n,tp)-n/tp)
res['H timeRev (exp)']=simplify(H(lambda x:exp(-h*x)*(2+sin(x)),t)+H(lambda x:exp(h*x)*(2+sin(-x)),-t))
res['q deSitter']=simplify(q(lambda x:exp(h*x),t)+1)
res['q powerLaw']=simplify(q(lambda x:x**n,tp)-(1-n)/n)
tn=symbols('tn',negative=True)
res['q crunch']=simplify(q(lambda x:(-x)**n,tn)-(1-n)/n)
res['q eds']=simplify(q(lambda x:x**Rational(2,3),tp)-Rational(1,2))
# LCDM checks: H^2 = H0^2 (Om (a0/a)^3 + 1 - Om)
def lcdm(a,Om,T0,T):
    return simplify(H(a,T)**2 - H(a,T0)**2*(Om*(a(T0)/a(T))**3+1-Om))
t0p=symbols('t0p',positive=True)
res['LCDM eds']=lcdm(lambda x:x**Rational(2,3),1,t0p,tp)
res['LCDM sinh']=simplify(lcdm(lambda x:sinh(x)**Rational(2,3),1/cosh(t0p)**2,t0p,tp).rewrite(exp))
res['LCDM sin']=simplify(lcdm(lambda x:sin(x)**Rational(2,3),1/cos(t0p)**2,t0p,tp))
for k,v in res.items(): print(k, v)
# numeric for sin case at sample points
import math
f=lambda T: (2/3)/math.tan(T)
for T0,T in [(0.7,0.5),(1.2,1.4),(0.3,0.31)]:
    Om=1/math.cos(T0)**2
    print('num sin',f(T)**2 - f(T0)**2*(Om*(math.sin(T0)**2/math.sin(T)**2)+1-Om))
g=lambda T:(2/3)/math.tanh(T)
for T0,T in [(0.7,0.5),(2.0,3.0)]:
    Om=1/math.cosh(T0)**2
    print('num sinh',g(T)**2 - g(T0)**2*(Om*(math.sinh(T0)**2/math.sinh(T)**2)+1-Om))
# limit H -> sqrt(Lambda_eff): H_inf=2/3 => (3/2)sqrt(Lambda_eff)=1 with Lambda_eff=H_inf^2 (not Einstein Lambda/3)
