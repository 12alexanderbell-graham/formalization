# Referee: independent derivation of F(R0), F''(R0), F'''(R0) from the metric f(R) FLRW equations
# (flat, dust, 8piG=1, rho0 = 3 H0^2 Omega), Taylor f to cubic order around R0 (f''''=0),
# then eta20/eta30 along (11.41) and alternative readings.
import sympy as sp, itertools
t,H0,O,e = sp.symbols('t H0 Omega epsilon', positive=True)
q,j,s,l,f0,f1,f2,f3 = sp.symbols('q j s l f0 f1 f2 f3')
N=6
a = 1 + H0*t - q*H0**2*t**2/2 + j*H0**3*t**3/6 + s*H0**4*t**4/24 + l*H0**5*t**5/120
ser = lambda x: sp.series(x, t, 0, N).removeO()
H = ser(sp.diff(a,t)/a)
R = ser(6*(sp.diff(H,t) + 2*H**2))
R0 = R.subs(t,0); dR = sp.expand(R - R0)
fp = f1 + f2*dR + f3/2*dR**2          # f'(R(t))
f  = f0 + f1*dR + f2/2*dR**2 + f3/6*dR**3
rho = 3*H0**2*O*ser(1/a**3)
E1 = ser(3*fp*H**2 - rho - (R*fp - f)/2 + 3*H*sp.diff(fp,t))
E2 = ser(2*fp*sp.diff(H,t) + rho + sp.diff(fp,t,2) - H*sp.diff(fp,t))
eqs = [E1.subs(t,0), sp.diff(E1,t).subs(t,0), sp.diff(E1,t,2).subs(t,0)]
eqs2 = [E1.subs(t,0), E2.subs(t,0), sp.diff(E2,t).subs(t,0)]
def solve(eqs, f1v):
    sol = sp.solve([sp.expand(x.subs(f1,f1v)) for x in eqs],[f0,f2,f3],dict=True)[0]
    return sol
sol = solve(eqs, 1); solb = solve(eqs2, 1)
print("E1-derivs vs E1,E2,E2' agree:", [sp.simplify(sol[k]-solb[k]) for k in (f0,f2,f3)])
# compare with review's P/Q and corrected R
P0=(j-q-2)*l-(3*s+7*j+6*q**2+41*q+22)*s-((3*q+16)*j+20*q**2+64*q+12)*j-(3*q**4+25*q**3+96*q**2+72*q+20)
Q0=(q**2-j*q+2*q)*l+(3*q*s+(4*q+6)*j+6*q**3+44*q**2+22*q-12)*s+(2*j**2+(3*q**2+10*q-6)*j+17*q**3+52*q**2+54*q+36)*j+(3*q**5+28*q**4+118*q**3+72*q**2-76*q-64)
P2=9*s+6*j+9*q**2+66*q+42
Q2=-(6*(q+1)*s+(2*j-2*(1-q))*j+6*q**3+50*q**2+74*q+32)
P3=3*l+3*s-9*(q+4)*j-(45*q**2+78*q+12)
Q3=-(2*(1+q)*l+2*(j+q)*s-(2*j+4*q**2+12*q+6)*j-(30*q**3+84*q**2+78*q+24))
Rc=(j-q-2)*l-(3*s-2*j+6*q**2+50*q+40)*s-((3*q+10)*j+11*q**2+4*q-18)*j-(3*q**4+34*q**3+180*q**2+246*q+104)
print("F  vs (11.21) w/ corrected R:", sp.simplify(sol[f0]/(6*H0**2) + (P0*O+Q0)/Rc))
print("F'' vs (11.23):", sp.simplify(sol[f2]*6*H0**2 + (P2*O+Q2)/Rc))
print("F'''vs (11.24):", sp.simplify(sol[f3]*36*H0**4 + (P3*O+Q3)/((j-q-2)*Rc)))
qL=sp.Rational(3,2)*O-1; jL=1; sL=1-sp.Rational(9,2)*O; lL=1+3*O+sp.Rational(27,2)*O**2
prD=(3*(9*O+74)*O-556)*O**2+16
pr20=(64-6*O*(9*O+8))/prD/27; pr30=(6*((81*O-110)*O+40)*O+16)/prD/(243*O**2)
def etas(so):
    return so[f2]*H0**4/so[f0], so[f3]*H0**6/so[f0]
def coeff(expr, sub, var=e):
    x = expr.subs(sub, simultaneous=True)
    x0 = sp.simplify(x.subs(var,0))
    return x0, sp.factor(sp.simplify(sp.diff(x,var).subs(var,0)))
def report(name, c20, c30, z20=0, z30=0):
    m20 = sp.simplify(c20-pr20)==0; m30 = sp.simplify(c30-pr30)==0
    v=[(float(sp.N(c20.subs(O,w))),float(sp.N(c30.subs(O,w)))) for w in (sp.Rational(41,1000),sp.Rational(1,4))]
    print(f"{name}: eta(0)=({z20},{z30}) c20={c20} | c30={c30} | vals={v} | match printed: {m20},{m30}")
e20,e30 = etas(sol)
mult = {q:qL*(1+e), j:jL*(1+e), s:sL*(1+e), l:lL*(1+e)}
z20,c20 = coeff(e20,mult); z30,c30 = coeff(e30,mult)
report("A common-eps multiplicative (program reading)", c20, c30, z20, z30)
# B: additive eps
add = {q:qL+e, j:jL+e, s:sL+e, l:lL+e}
z20,c20 = coeff(e20,add); z30,c30 = coeff(e30,add); report("B additive", c20,c30,z20,z30)
# C: f'(R0) = 1/(1+eps) in addition (upstream v1 Sect. IV / HS discussion)
solC = solve(eqs, 1/(1+e)); e20C,e30C = etas(solC)
z20,c20 = coeff(e20C,mult); z30,c30 = coeff(e30C,mult); report("C mult + f'=1/(1+eps)", c20,c30,z20,z30)
z20,c20 = coeff(e20C,{}); z30,c30 = coeff(e30C,{})
c20=sp.factor(sp.diff(e20C.subs({q:qL,j:jL,s:sL,l:lL}),e).subs(e,0)); c30=sp.factor(sp.diff(e30C.subs({q:qL,j:jL,s:sL,l:lL}),e).subs(e,0))
report("C' only f'=1/(1+eps) at LCDM", c20,c30)
# D: subsets / signs of directions
syms=[q,j,s,l]; base={q:qL,j:jL,s:sL,l:lL}
dirs20=[]; dirs30=[]
for x in syms:
    sub=dict(base); sub[x]=base[x]*(1+e)
    dirs20.append(sp.simplify(sp.diff(e20.subs(sub,simultaneous=True),e).subs(e,0)))
    dirs30.append(sp.simplify(sp.diff(e30.subs(sub,simultaneous=True),e).subs(e,0)))
print("partials eta20:", [sp.factor(d) for d in dirs20]); print("partials eta30:", [sp.factor(d) for d in dirs30])
hits=[]
for signs in itertools.product([-1,0,1],repeat=4):
    if all(x==0 for x in signs): continue
    c20=sum(sg*d for sg,d in zip(signs,dirs20)); c30=sum(sg*d for sg,d in zip(signs,dirs30))
    for w in (sp.Rational(41,1000),sp.Rational(1,4)):
        pass
    v20=[float(c20.subs(O,w)) for w in (0.041,0.25)]; v30=[float(c30.subs(O,w)) for w in (0.041,0.25)]
    if abs(v20[0]-0.152)<0.03 or abs(v30[0]-4.02)<0.5: hits.append((signs,v20,v30))
print("sign/subset combos near printed at 0.041:", hits)
# E: rho normalised differently: rho0 = 3 H0^2 Omega * f'(R0)?  (irrelevant when f'=1) ; Omega in rho perturbed?
eO=sp.symbols('eO')
z20,c20 = coeff(e20.subs(O,O*(1+e)) if False else e20, {**mult}); 
# F: ratios with printed R in F and corrected R in F'' (non-cancelling R)
Rp=(j-q-2)*l-(3*s-2*j+6*q**2+50*q+40)*s+((3*q+10)*j+11*q**2+4*q+18)*j-(3*q**4+34*q**3+246*q+104)
for nm,(Ra,Rb) in {"F''(Rc)/F(Rp)":(Rc,Rp),"F''(Rp)/F(Rc)":(Rp,Rc)}.items():
    x20 = ((P2*O+Q2)/Ra)/(36*(P0*O+Q0)/Rb)
    x30 = ((P3*O+Q3)/((j-q-2)*Ra))/(216*(P0*O+Q0)/Rb)
    _,c20=coeff(x20,mult); _,c30=coeff(x30,mult); report("F "+nm,c20,c30)
