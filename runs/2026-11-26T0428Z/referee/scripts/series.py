import sympy as sp
s=sp.symbols('s'); N=12
c=sp.symbols('c1:%d'%N)
w=sum(c[i-1]*s**(2*i) for i in range(1,N//2+1))
expr=sp.expand(s*sp.diff(w,s,2)+2*sp.diff(w,s)+s*sp.series(sp.exp(w),s,0,2*(N//2)+2).removeO())
sol=sp.solve([expr.coeff(s,2*i-1) for i in range(1,N//2+1)],c[:N//2],dict=True)[0]
print([sol[c[i]] for i in range(N//2)])
