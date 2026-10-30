import sympy as sp
O,w0,wa,H=sp.symbols('Omega w0 wa H')
p=-3*(1+w0+wa)
N=7
A=sp.symbols('a0:%d'%N); X=sp.symbols('x0:%d'%N); Y=sp.symbols('y0:%d'%N)
def D(e):
    return sum(sp.diff(e,A[i])*A[i+1]+sp.diff(e,X[i])*X[i+1]+sp.diff(e,Y[i])*Y[i+1] for i in range(N-1))
# a0=1 normalisation at t0 (values: a=1,x=1,y=1, adot=H)
Z=[A[0]*A[1]**2 - H**2*(O + (1-O)*A[0]**3*X[0]*Y[0]),   # squared law times a^3 ... (a ȧ² = H²(Ω + (1-Ω) a³ x y))
   A[0]*X[1]-p*X[0]*A[1],
   Y[1]-3*wa*Y[0]*A[1]]
vals={A[0]:1,X[0]:1,Y[0]:1,A[1]:H}
# first derivative of Z0 = ȧ * R0 ; divide
dZ0=sp.expand(D(Z[0]).subs(X[1],p*X[0]*A[1]/A[0]).subs(Y[1],3*wa*Y[0]*A[1]))
R0=sp.factor(dZ0)
print('dZ0 factor:',R0)
R=sp.expand(sp.cancel(dZ0/(-A[1])))  # R0 (sign irrelevant)
eqs=[R]; Zx=[Z[1]]; Zy=[Z[2]]
for k in range(3):
    eqs.append(sp.expand(D(eqs[-1])))
for k in range(4):
    Zx.append(sp.expand(D(Zx[-1]))); Zy.append(sp.expand(D(Zy[-1])))
v=dict(vals)
# order: solve x1,y1 from Zx0,Zy0; a2 from R0; x2,y2 from Zx1,Zy1; a3 from R1 ...
for k in range(4):
    for (Z_,unk) in ((Zx[k],X[k+1]),(Zy[k],Y[k+1])):
        v[unk]=sp.simplify(sp.solve(Z_.subs(v),unk)[0])
    v[A[k+2]]=sp.simplify(sp.solve(eqs[k].subs(v),A[k+2])[0])
l=sp.expand(sp.simplify(v[A[5]]/H**5))
printed_l=sp.Rational(35,2)+(1-O)/4*(213+(7-O)*wa)*wa+(1-O)/4*(489+9*(82-21*O)*wa)*w0+sp.Rational(9,2)*(1-O)*(67-21*O+sp.Rational(3,2)*(23-11*O)*wa)*w0**2+sp.Rational(27,4)*(1-O)*(47-24*O)*w0**3+sp.Rational(81,2)*(1-O)*(3-2*O)*w0**4
print('printed - system l0:', sp.factor(sp.expand(printed_l-l)))
