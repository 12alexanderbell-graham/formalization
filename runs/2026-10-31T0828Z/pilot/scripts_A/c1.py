from sympy import *
R,a,b,u,w,T,v,x=symbols('R a b u w T v x')
D=v**2+u*b*v+w*b**2
P=R*T/(v-b)-a/D
P1=diff(P,v);P2=diff(P,v,2)
# eliminate RT: from P1=0
RT=solve(P1.subs(R*T,symbols('r')),symbols('r'))
r=symbols('r')
P1r=diff(r/(v-b)-a/D,v);P2r=diff(r/(v-b)-a/D,v,2)
sol=solve(P1r,r)[0]
e=simplify(P2r.subs(r,sol))
print(factor(e))
num=numer(together(e))
print(factor(num))
# compare to claim
cl=v**3-3*b*v**2-3*(u+w)*b**2*v-(u**2+u*w-w)*b**3
print(simplify(expand(num)/cl))
critc=lambda x: x**3-3*x**2-3*(u+w)*x-(u**2+u*w-w)
print(expand(cl.subs(v,x*b)/b**3 - critc(x)))
