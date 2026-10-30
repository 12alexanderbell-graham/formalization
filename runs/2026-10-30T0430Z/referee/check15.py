import sympy as sp
z,Om,w0,wa,l=sp.symbols('z Omega_m w0 wa l')
E2=Om*(1+z)**3+(1-Om)*(1+z)**(3*(1+w0+wa))*sp.exp(-3*wa*z/(1+z))
H=sp.sqrt(E2)
d=[sp.simplify(sp.diff(H,z,k).subs(z,0)) for k in range(5)]
q,j,s=sp.symbols('q j s')
# paper Eqs 12-15 at z=0, H0=1
eqs=[sp.Eq(d[1],1+q),sp.Eq(d[2],-q**2+j),sp.Eq(d[3],3*q**2+3*q**3-4*q*j-3*j-s),
     sp.Eq(d[4],-12*q**2-24*q**3-15*q**4+32*q*j+25*q**2*j+7*q*s+12*j-4*j**2+8*s+l)]
sol=sp.solve(eqs,[q,j,s,l],dict=True)[0]
print('wa^2 coeff of l0 via paper Eq.15:',sp.factor(sp.Poly(sp.expand(sol[l]),wa,w0).coeff_monomial(wa**2)))
