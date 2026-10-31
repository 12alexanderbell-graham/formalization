from sympy import *
t,q,j,s,l=symbols('t q j s l')
a=1+t-q*t**2/2+j*t**3/6+s*t**4/24+l*t**5/120
H=series(diff(a,t)/a,t,0,5).removeO()
R=expand(-6*(diff(H,t)+2*H**2))
print([factor(diff(R,t,n).subs(t,0)) for n in range(4)])
print(expand(diff(R,t,3).subs(t,0)+6*(l-s+2*(q+4)*j-6*(3*q+8)*q-24)))
print(expand(diff(R,t,3).subs(t,0)-6*(l-s+2*(q+4)*j-6*(3*q+8)*q-24)*(-1)))
