import sympy as sp
T,H,c,a0,K,q,j,s,l,z,y,Om,Tp = sp.symbols('T H c a0 K q j s l z y Omega0 Tp')
N=6
ratio = 1 - H*T - q*H**2*T**2/2 - j*H**3*T**3/6 + s*H**4*T**4/24 - l*H**5*T**5/120
onepz = sp.series(1/ratio, T, 0, N).removeO()
chi = sp.integrate(sp.series(c/(a0*ratio.subs(T,Tp)),Tp,0,N).removeO(),(Tp,0,T))
r0 = chi - K*chi**3/6 + K**2*chi**5/120
dL = sp.expand(sp.series(onepz*a0*r0, T, 0, N+1).removeO())
zT = sp.expand(onepz-1)
bs=[sp.Symbol('b%d'%i) for i in range(1,N+1)]
Tz = sum(b*z**i for i,b in enumerate(bs,1))
eqs = sp.expand(sp.series(zT.subs(T,Tz),z,0,N+1).removeO()) - z
sol = sp.solve([eqs.coeff(z,i) for i in range(1,N+1)], bs, dict=True)[0]
Tz = Tz.subs(sol)
dLz = sp.expand(sp.series(dL.subs(T,Tz), z, 0, N).removeO().subs(K,(Om-1)*H**2*a0**2/c**2))
dLy = sp.expand(sp.series(dLz.subs(z, y/(1-y)), y, 0, N).removeO())
dAy = sp.expand(sp.series(dLy*(1-y)**2, y,0,N).removeO())
DL=[sp.expand(dLy.coeff(y,i)*H/c) for i in range(1,N)]
DA=[sp.expand(dAy.coeff(y,i)*H/c) for i in range(1,N)]
R=sp.Rational
P = {
 'L2 (10.54)': -R(1,6)*(12-5*q+3*q**2-j-Om),
 'L3 (10.55)': R(1,24)*(52-20*q+21*q**2-15*q**3-7*j+10*q*j+s-2*Om*(1+3*q)),
 'L4 (10.56-57)': R(1,120)*(359-184*q+186*q**2-135*q**3+105*q**4+90*q*j-105*q**2*j-15*q*s-57*j+10*j**2+9*s-l-5*Om*(17-6*q+9*q**2-2*j)),
 'A1 (10.59)': -R(1,2)*(1+q),
 'A2 (10.60)': -R(1,6)*(-q-3*q**2+j+Om),
 'A3 (10.61)': -R(1,24)*(-2*q+3*q**2+15*q**3-j-10*q*j-s+2*Om),
 'A4 (10.62-63)': -R(1,120)*(1-6*q+9*q**2-15*q**3-105*q**4+10*q*j+105*q**2*j+15*q*s-3*j-10*j**2+s+l+5*Om),
}
D={'L2 (10.54)':DL[2],'L3 (10.55)':DL[3],'L4 (10.56-57)':DL[4],'A1 (10.59)':DA[1],'A2 (10.60)':DA[2],'A3 (10.61)':DA[3],'A4 (10.62-63)':DA[4]}
for k in P:
    print(k, " derived:", sp.factor(D[k]*{2:6,3:24,4:120,1:2}[int(k[1])]), "/", {2:6,3:24,4:120,1:2}[int(k[1])])
    print("    derived - printed =", sp.factor(sp.expand(D[k]-P[k])))
# Mattig check (dust, Lambda=0, any curvature): H0 dL/c = 2[Om z + (Om-2)(sqrt(1+Om z)-1)]/Om^2, Omega0 = Om
Omn=sp.Rational(3,10)
mat = 2*(Omn*z+(Omn-2)*(sp.sqrt(1+Omn*z)-1))/Omn**2
maty = sp.series(mat.subs(z,y/(1-y)),y,0,N).removeO()
# cosmographic params for dust: compute from H^2 = Om a^-3 + (1-Om) a^-2 (H0=1)
A=sp.symbols('A',positive=True)
Hf = sp.sqrt(Omn*A**-3+(1-Omn)*A**-2)
# d/dt = A*H d/dA ; derivatives of a
d1 = A*Hf
d=[A,d1]
for k in range(4): d.append(sp.simplify(A*Hf*sp.diff(d[-1],A)))
vals={q:-d[2].subs(A,1), j:d[3].subs(A,1), s:d[4].subs(A,1), l:d[5].subs(A,1), Om:Omn}
print("dust Om=0.3 params:", vals)
for i in range(1,N):
    print("y^%d Mattig:"%i, sp.nsimplify(maty.coeff(y,i)), " derived:", sp.simplify(DL[i-1].subs(vals)) if i>1 else 1,
          " printed:", sp.simplify(list(P.values())[i-3].subs(vals)) if 3<=i<=5 else "")
