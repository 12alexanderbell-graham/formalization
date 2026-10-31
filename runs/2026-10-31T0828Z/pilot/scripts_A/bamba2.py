from sympy import *
import pickle
t,q,j,s,l,k,z,y,Om=symbols('t q j s l k z y Omega')
Dl,Da,tzs,dlz=pickle.load(open('bamba_z.pkl','rb'))
N=6
def trunc(e,v,n=N):
    e=expand(e); return sum(e.coeff(v,i)*v**i for i in range(n+1))
zy=trunc(series(y/(1-y),y,0,N+1).removeO(),y)
def comp(f):
    res=0;p=1
    for i in range(0,N+1):
        res+=f.coeff(z,i)*p
        p=trunc(p*zy,y)
    return trunc(res,y)
dly=comp(expand(dlz))
dae=trunc(dlz*trunc(series(1/(1+z)**2,z,0,N+1).removeO(),z),z)
day=comp(dae)
def coeffs(e): return [factor(expand(e).coeff(y,n).subs(k,Om-1)) for n in range(1,6)]
CL=coeffs(dly); CA=coeffs(day)
pickle.dump((CL,CA),open('bamba_y.pkl','wb'))
for n,c in enumerate(CL): print('DLy',n,c)
for n,c in enumerate(CA): print('DAy',n,c)
# printed
pD2=-Rational(1,6)*(12-5*q+3*q**2-j-Om)
pD3=Rational(1,24)*(52-20*q+21*q**2-15*q**3-7*j+10*q*j+s-2*Om*(1+3*q))
pD4=Rational(1,120)*(359-184*q+186*q**2-135*q**3+105*q**4+90*q*j-105*q**2*j-15*q*s-57*j+10*j**2+9*s-l-5*Om*(17-6*q+9*q**2-2*j))
print('D1y', CL[0], 'printed',-Rational(1,2)*(-3+q))
print('D2 diff',factor(CL[1]-pD2), 'plus-sign check', simplify(CL[1]+pD2))
print('D3 diff',factor(CL[2]-pD3))
print('D4 diff',factor(CL[3]-pD4))
pA1=-Rational(1,2)*(1+q); pA2=-Rational(1,6)*(-q-3*q**2+j+Om)
pA3=-Rational(1,24)*(-2*q+3*q**2+15*q**3-j-10*q*j-s+2*Om)
pA4=-Rational(1,120)*(1-6*q+9*q**2-15*q**3-105*q**4+10*q*j+105*q**2*j+15*q*s-3*j-10*j**2+s+l+5*Om)
print('DA1',CA[0],pA1)
print('DA2 diff',factor(CA[1]-pA2))
print('DA3 diff',factor(CA[2]-pA3))
print('DA4 diff',factor(CA[3]-pA4))
print('-----')
d4=CL[3]-pD4
d4=expand(d4)
print('D4 diff at Om=1', simplify(d4.subs(Om,1)))
print('D4 diff factor in (Om-1):', factor(d4))
x=symbols('x')
print(expand(d4.subs(Om,x+1)))
print('expected', expand(Rational(1,120)*x**2+Rational(5,12)*q*x))
da4=expand(CA[3]-pA4)
print('DA4y diff at Om=1', simplify(da4.subs(Om,1)))
# DA3 with correctDA3
pA3c=pA3+q*(Om-1)/4
print('DA3 corrected diff', factor(CA[2]-pA3c))
print('DA2y diff', factor(CA[1]-pA2))
print('DA4y diff', expand(CA[3]-pA4).subs(Om,x+1).expand())
