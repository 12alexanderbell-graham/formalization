# Blind derivation of cosmography series coefficients (sympy). H0 = a0 = c = 1.
import sympy as sp
q,j,s,l,k,z,y,tau,eps,Om = sp.symbols('q j s l k z y tau epsilon Omega')
N=6
# scale factor a(tau)/a0, tau = H0 (t - t0)
A = 1 + tau - q*tau**2/2 + j*tau**3/6 + s*tau**4/24 + l*tau**5/120
def trunc(e,var,n):
    e=sp.expand(e)
    return sum(e.coeff(var,i)*var**i for i in range(n))
def inv_series(P,var,n):
    # 1/P for P=1+..., truncated
    u=sp.expand(P-1); r=1; term=1
    for i in range(1,n):
        term=trunc(-term*u,var,n); r+=term
    return sp.expand(r)
def powser(base,expo,var,n):
    # (1+base)^expo truncated, base=O(var)
    r=0; term=1
    for i in range(n):
        r+=sp.binomial(expo,i)*term; term=trunc(term*base,var,n)
    return sp.expand(r)
# 1+z = 1/A  -> z(tau); invert for tau(z)
zt = inv_series(A,tau,N)-1
cs = sp.symbols('c1:6')
tz = sum(c*z**(i+1) for i,c in enumerate(cs))
eq = sp.expand(trunc(zt.subs(tau,tz),z,N)-z)
sol={}
for n in range(1,6):
    cn=sp.expand(eq.coeff(z,n).subs(sol))
    sol[cs[n-1]]=sp.solve(cn,cs[n-1])[0]
tauz = sp.expand(tz.subs(sol))
lookback = sp.expand(-tauz)                       # H0 (t0 - t)
D = [sp.expand(lookback.coeff(z,n+1)) for n in range(1,5)]  # D1..D4 ( /z )
assert sp.expand(lookback.coeff(z,1))==1
correctD4 = sp.expand(D[3])
# comoving distance chi = int_tau^0 dtau'/A
inv = inv_series(A,tau,5)
chi_tau = sp.expand(-sp.integrate(inv,(tau,0,tau)) * (-1))  # int_tau^0 = -int_0^tau
chi_tau = sp.expand(-sp.integrate(inv,tau))               # F(0)-F(tau) with F(0)=0
chi = trunc(chi_tau.subs(tau,tauz),z,N)
def S(c):  # sin(sqrt K c)/sqrt K, K=k
    return c - k*c**3/6 + k**2*c**5/120
dL = sp.expand(trunc((1+z)*S(chi),z,N))
def bracket_z(expr):
    e = sp.expand(trunc(expr,z,N))
    return [sp.expand(e.coeff(z,n+1)) for n in range(0,5)]   # z^1..z^5 coefficients
def to_y(expr_z):
    zy=sum(y**i for i in range(1,N))
    e=0; pw=1
    for i in range(1,N):
        pw=trunc(pw*zy,y,N); e+=expr_z.coeff(z,i)*pw
    e=sp.expand(e)
    return [sp.expand(e.coeff(y,n+1)) for n in range(0,5)]
dA = sp.expand(trunc(dL*powser(z,-2,z,N),z,N))
dQ = sp.expand(trunc(dL*powser(z,sp.Rational(-3,2),z,N),z,N))
Lz = bracket_z(dL); Az = bracket_z(dA)
Ly = to_y(dL); Ay = to_y(dA); Qy = to_y(dQ)
assert Lz[0]==1 and Ly[0]==1
Ok = {k:Om-1}   # Omega = 1 + k
res = {}
res['correctD4']=correctD4
res['correctD2y']=sp.expand(Ly[2].subs(Ok))
res['correctD3y']=sp.expand(Ly[3].subs(Ok))
res['correctD4y']=sp.expand(Ly[4].subs(Ok))
res['correctDA3']=sp.expand(Ay[3].subs(Ok))
res['correctDA4']=sp.expand(Ay[4].subs(Ok))
res['correctDL4z']=sp.expand(Lz[4])
res['correctDA4z']=sp.expand(Az[4])
res['correctQ2']=sp.expand(Qy[2].subs(Ok))
res['D1y']=sp.expand(Ly[1]); res['Qy1']=Qy[1]
# F(R) ratios
def P0(q,j,s,l): return (j-q-2)*l-(3*s+7*j+6*q**2+41*q+22)*s-((3*q+16)*j+20*q**2+64*q+12)*j-(3*q**4+25*q**3+96*q**2+72*q+20)
def Q0(q,j,s,l): return (q**2-j*q+2*q)*l+(3*q*s+(4*q+6)*j+6*q**3+44*q**2+22*q-12)*s+(2*j**2+(3*q**2+10*q-6)*j+17*q**3+52*q**2+54*q+36)*j+3*q**5+28*q**4+118*q**3+72*q**2-76*q-64
def P2(q,j,s): return 9*s+6*j+9*q**2+66*q+42
def Q2(q,j,s): return -(6*(q+1)*s+(2*j-2*(1-q))*j+6*q**3+50*q**2+74*q+32)
def P3(q,j,s,l): return 3*l+3*s-9*(q+4)*j-(45*q**2+78*q+12)
def Q3(q,j,s,l): return -(2*(1+q)*l+2*(j+q)*s-(2*j+4*q**2+12*q+6)*j-(30*q**3+84*q**2+78*q+24))
qL=sp.Rational(3,2)*Om-1; sL=1-sp.Rational(9,2)*Om; lL=1+3*Om+sp.Rational(27,2)*Om**2
fq,fj,fs,fl=qL*(1+eps),(1+eps),sL*(1+eps),lL*(1+eps)
den0=P0(fq,fj,fs,fl)*Om+Q0(fq,fj,fs,fl)
e20=(P2(fq,fj,fs)*Om+Q2(fq,fj,fs))/(36*den0)
e30=(P3(fq,fj,fs,fl)*Om+Q3(fq,fj,fs,fl))/(216*(fj-fq-2)*den0)
print('eta at 0:',sp.cancel(sp.together(e20.subs(eps,0))),sp.cancel(sp.together(e30.subs(eps,0))),flush=True)
res['correct20']=sp.factor(sp.cancel(sp.together(sp.diff(e20,eps).subs(eps,0))))
res['correct30']=sp.factor(sp.cancel(sp.together(sp.diff(e30,eps).subs(eps,0))))
for n,v in res.items(): print(n,'=',v)
import pickle; pickle.dump({n:str(v) for n,v in res.items()},open('/tmp/blindB/res.pkl','wb'))
# --- numeric verification on exact models ---
import mpmath as mp
mp.mp.dps=40
def check(name,afun,t0,kval):
    # afun sympy expr in t; compute q,j,s,l,H0,a0 exactly
    t=sp.symbols('t')
    a=afun(t); d=[sp.diff(a,t,n).subs(t,t0) for n in range(6)]
    H0=d[1]/d[0]; vals={q:-d[2]*d[0]/d[1]**2, j:d[3]/(d[0]*H0**3), s:d[4]/(d[0]*H0**4), l:d[5]/(d[0]*H0**5)}
    a0=d[0]; kk=kval/(H0**2*a0**2); vals[k]=kk; vals[Om]=1+kk
    af=sp.lambdify(t,a,'mpmath'); H0n=mp.mpf(sp.N(H0,40)); a0n=mp.mpf(sp.N(a0,40)); Kn=mp.mpf(kval)
    print(name,{str(x):sp.N(vals[x],8) for x in (q,j,s,l)})
    def exact(zz):
        # find t with a0/a(t)=1+z
        tt=mp.findroot(lambda x: a0n/af(x)-1-zz, float(t0)-0.1*float(zz)/float(H0n) if True else t0, tol=1e-35)
        chi=mp.quad(lambda x:1/af(x),[tt,mp.mpf(sp.N(t0,40))])
        Sk=mp.sin(mp.sqrt(Kn)*chi)/mp.sqrt(Kn) if Kn>0 else (chi if Kn==0 else mp.sinh(mp.sqrt(-Kn)*chi)/mp.sqrt(-Kn))
        dl=a0n*(1+zz)*Sk
        return dict(look=H0n*(mp.mpf(sp.N(t0,40))-tt),dL=H0n*dl,dA=H0n*dl/(1+zz)**2,dQ=H0n*dl/(1+zz)**mp.mpf(1.5))
    D1_=-(1+vals[q]/2); 
    for zz in [mp.mpf('0.02'),mp.mpf('0.01'),mp.mpf('0.005')]:
        e=exact(zz); yy=zz/(1+zz)
        # lookback
        Dn=[mp.mpf(sp.N(x.subs(vals),40)) for x in D]
        lb=zz*(1+Dn[0]*zz+Dn[1]*zz**2+Dn[2]*zz**3+Dn[3]*zz**4)
        # dL in y, full order-4 from derived coefficients
        c=[mp.mpf(sp.N(Ly[i].subs(vals),40)) for i in range(5)]
        dly=yy*(1+c[1]*yy+c[2]*yy**2+c[3]*yy**3+c[4]*yy**4)
        ca=[mp.mpf(sp.N(Ay[i].subs(vals),40)) for i in range(5)]
        day=yy*(1+ca[1]*yy+ca[2]*yy**2+ca[3]*yy**3+ca[4]*yy**4)
        cz=[mp.mpf(sp.N(Lz[i].subs(vals),40)) for i in range(5)]
        dlz=zz*(1+cz[1]*zz+cz[2]*zz**2+cz[3]*zz**3+cz[4]*zz**4)
        cz2=[mp.mpf(sp.N(Az[i].subs(vals),40)) for i in range(5)]
        daz=zz*(1+cz2[1]*zz+cz2[2]*zz**2+cz2[3]*zz**3+cz2[4]*zz**4)
        cq=[mp.mpf(sp.N(Qy[i].subs(vals),40)) for i in range(3)]
        dqy=yy*(1+cq[1]*yy+cq[2]*yy**2)
        print(' z=',zz,'resid/z^5 look,dLy,dAy,dLz,dAz ; dQ/y^3:',
          mp.nstr((lb-e['look'])/zz**5,5),mp.nstr((dly-e['dL'])/yy**6,5),mp.nstr((day-e['dA'])/yy**6,5),
          mp.nstr((dlz-e['dL'])/zz**6,5),mp.nstr((daz-e['dA'])/zz**6,5),mp.nstr((dqy-e['dQ'])/yy**4,5))
check('deSitter flat',lambda t:sp.exp(t),sp.Integer(0),0)
check('matter flat',lambda t:t**sp.Rational(2,3),sp.Integer(1),0)
check('Milne',lambda t:t,sp.Integer(1),-1)
check('sin(t) K=1',lambda t:sp.sin(t),sp.Rational(1,2),1)
check('sinh+t^2 K=-0.7',lambda t:sp.sinh(t)+t**2/3,sp.Rational(7,10),sp.Rational(-7,10))
