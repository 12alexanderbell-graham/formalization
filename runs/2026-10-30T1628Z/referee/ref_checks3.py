# Referee: (i) LCDM cosmographic values (11.39) from H^2 = H0^2(Om a^-3 + 1 - Om);
# (ii) sign map between conventions R=+6(Hdot+2H^2) and review (11.6) R=-6(...);
# (iii) size of exact eta vs linear along the family at Omega=0.041, 0.25.
import sympy as sp, mpmath
t,O,x=sp.symbols('t Omega x',positive=True)
# (i) use a as variable: d/dt = a H d/da ; H(a)=sqrt(Om a^-3+1-Om), H0=1
a=sp.symbols('a',positive=True)
H=sp.sqrt(O*a**-3+1-O)
D=lambda f: sp.simplify(a*H*sp.diff(f,a))
adot=a*H; a2=D(adot); a3=D(a2); a4=D(a3); a5=D(a4)
sub={a:1}
print("q0=",sp.simplify(-(a2*a/adot**2).subs(sub)),"j0=",sp.simplify((a3*a**2/adot**3).subs(sub)),
      "s0=",sp.simplify((a4*a**3/adot**4).subs(sub)),"l0=",sp.expand(sp.simplify((a5*a**4/adot**5).subs(sub))))

# (iii) exact eta along the family (review's own P/Q; R cancels)
e,q,j,s,l=sp.symbols('epsilon q j s l')
P0=(j-q-2)*l-(3*s+7*j+6*q**2+41*q+22)*s-((3*q+16)*j+20*q**2+64*q+12)*j-(3*q**4+25*q**3+96*q**2+72*q+20)
Q0=(q**2-j*q+2*q)*l+(3*q*s+(4*q+6)*j+6*q**3+44*q**2+22*q-12)*s+(2*j**2+(3*q**2+10*q-6)*j+17*q**3+52*q**2+54*q+36)*j+(3*q**5+28*q**4+118*q**3+72*q**2-76*q-64)
P2=9*s+6*j+9*q**2+66*q+42
Q2=-(6*(q+1)*s+(2*j-2*(1-q))*j+6*q**3+50*q**2+74*q+32)
P3=3*l+3*s-9*(q+4)*j-(45*q**2+78*q+12)
Q3=-(2*(1+q)*l+2*(j+q)*s-(2*j+4*q**2+12*q+6)*j-(30*q**3+84*q**2+78*q+24))
for Ov in (sp.Rational(41,1000),sp.Rational(1,4)):
    qL=sp.Rational(3,2)*Ov-1; sL=1-sp.Rational(9,2)*Ov; lL=1+3*Ov+sp.Rational(27,2)*Ov**2
    fam={q:qL*(1+e),j:1+e,s:sL*(1+e),l:lL*(1+e)}
    e20=sp.lambdify(e,((P2*Ov+Q2)/(36*(P0*Ov+Q0))).subs(fam,simultaneous=True))
    e30=sp.lambdify(e,((P3*Ov+Q3)/(216*(j-q-2)*(P0*Ov+Q0))).subs(fam,simultaneous=True))
    import numpy as np
    grid=np.linspace(-0.1,0.1,20001)
    v20=np.array([e20(x) for x in grid]); v30=np.array([e30(x) for x in grid])
    i20=np.argmax(abs(v20)); i30=np.argmax(abs(v30))
    print(f"Omega={float(Ov)}: max|eta20| on [-0.1,0.1] = {abs(v20[i20]):.4g} at eps={grid[i20]:.4f}; max|eta30| = {abs(v30[i30]):.4g} at eps={grid[i30]:.4f}")
    for x in (0.01,0.02,0.05,0.1,-0.05,-0.1):
        print(f"   eps={x}: eta20={e20(x):.5g}, eta30={e30(x):.5g}")
