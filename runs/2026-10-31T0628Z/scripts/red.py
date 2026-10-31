import sympy as sp
x=sp.symbols('x')
for name,u,w,targets in [('RK',1,0,{'Zc':sp.Rational(1,3),'Ob':x**2/3-x-1,'Oa':x/9}),('PR',2,-1,{'Zc':-3*x**2/64+5*x/32+sp.Rational(27,64),'Ob':9*x**2/64-15*x/32-sp.Rational(17,64),'Oa':sp.Rational(147,1024)*x**2-sp.Rational(165,512)*x-sp.Rational(523,1024)})]:
    f=x**3-3*x**2-3*(u+w)*x-(u**2+u*w-w); D=x**2+u*x+w; s=2*x+u
    N=(x-1)*s-D
    forms={'Zc':(x*N,(x-1)**2*s),'Ob':(N,(x-1)**2*s),'Oa':(D**2*N,(x-1)**4*s**2)}
    for k,(num,den) in forms.items():
        q,r=sp.div(sp.expand(num-targets[k]*den),f,x)
        print(name,k,'rem',r,'quot',q)
