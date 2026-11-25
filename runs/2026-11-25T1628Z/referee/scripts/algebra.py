import sympy as sp
x,y,s=sp.symbols('x y s')
u=1+x; v=2+y
Nw=7*x**2+(x+2*y)**2
xd=(1+x)*(-x-y); yd=(2+y)*x
Lq=x*yd-y*xd
Dq=-Nw-4*x*(4*x**2+4*x*y-y**2)
print("Dq == s dNw/ds:", sp.expand(sp.diff(Nw,x)*xd+sp.diff(Nw,y)*yd-Dq)==0)
print("identity:", sp.expand(28*(y-2*x)*Lq-((6*x+5*y)*Dq-2*Nw*(6*xd+5*yd)))==0)
g=2*u-v
print("1-cos^2:", sp.simplify(1-(-6*x-5*y)**2/(8*Nw) - 7*g**2/(8*Nw))==0)
print("dlog(uv^3):", sp.expand((u*(3-u-v))/u+3*(v*(u-1))/v - g))
print("g' at g=0:", sp.factor((2*u*(3-u-v)-v*(u-1)).subs(y,2*x)))
print("Nw at g=0:", sp.factor(Nw.subs(y,2*x)), " uv^3:", sp.factor((u*v**3).subs(y,2*x)))
print("Lq-Nw/4 linear part:", sp.expand(Lq-Nw/4))
