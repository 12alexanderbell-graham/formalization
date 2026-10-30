"""Part 2: (11.18)/(11.20) differentiation, (11.3)-(11.4) consistency, solution of the closed system
vs printed P0..Q3, R (11.25)-(11.31), variants with the misprinted (11.13)/(11.18), LCDM check (11.40),
CPL cosmography (11.35)-(11.39), epsilon expansions (11.42)-(11.45), quiescence roots (11.46)-(11.47).
Same conventions as secXI_check.py (H0=1, R=-6(Hdot+2H^2), kappa^2=1, F'(R0)=1)."""
import sympy as sp
t=sp.symbols('t')
q,j,s,l,Om,eps,w0,wa,z=sp.symbols('q0 j0 s0 l0 Omega_M epsilon w0 wa z')
H0=1
# ---------- (11.18): treat G_k(t)=F^(k)(R(t)) with dG_k/dt = G_{k+1} Rdot ----------
R=sp.Function('R')(t); H=sp.Function('H')(t); A=sp.Function('a')(t); Fz=sp.Function('F0')(t)
G={k:sp.Function(f'G{k}')(t) for k in range(1,6)}
def D(e):
    e=sp.diff(e,t)
    sub={sp.Derivative(G[k],t):G[k+1]*R.diff(t) for k in range(1,5)}
    sub[sp.Derivative(Fz,t)]=G[1]*R.diff(t)
    sub[sp.Derivative(A,t)]=A*H
    return sp.expand(e.subs(sub))
rhoM=3*Om*A**-3
N=rhoM+R.diff(t,2)*G[2]+R.diff(t)*(R.diff(t)*G[3]-H*G[2])
Hdot=-N/(2*G[1])
Hdd=D(Hdot)
R1,R2,R3=R.diff(t),R.diff(t,2),R.diff(t,3); Hd=H.diff(t)
def pr18(sg):
    return ((R1**2*G[3]+(R2-H*R1)*G[2]+rhoM)/(2*(R1*G[2])**-1*G[1]**2)
      -(R1**3*G[4]+(3*R1*R2-H*R1**2)*G[3])/(2*G[1])
      -((R3-H*R2+sg*Hd*R1)*G[2]-9*Om*H*A**-3)/(2*G[1]))
print("(11.18) printed (+Hdot Rdot) - derived :",sp.factor(sp.cancel(sp.together(pr18(+1)-Hdd))),flush=True)
print("(11.18) with -Hdot Rdot  - derived     :",sp.cancel(sp.together(pr18(-1)-Hdd)),flush=True)
# ---------- (11.3)/(11.4) ----------
rc=((Fz-R*G[1])/2-3*H*R1*G[2])/G[1]
wc=-1+(R2*G[2]+R1*(R1*G[3]-H*G[2]))/((Fz-R*G[1])/2-3*H*R1*G[2])
# use the Friedmann eq. only through Hdot from (11.5) and R=-6(Hdot+2H^2) is not needed: identity check
lhs=D(rc)+3*H*(1+wc)*rc
rhs=rhoM*R1*G[2]/G[1]**2
print("(11.3) lhs - rhs :",sp.cancel(sp.together(lhs-rhs)),flush=True)
# ---------- closed system ----------
R0=-6*(1-q); Rd1=-6*(j-q-2); Rd2=-6*(s+q**2+8*q+6)
Rd3_true=-6*(l-s-2*(q+4)*j-6*(3*q+8)*q-24)
Rd3_print=-6*(l-s+2*(q+4)*j-6*(3*q+8)*q-24)
Hd0=-(1+q); Hdd0=j+3*q+2
f0,f2,f3=sp.symbols('f0 f2 f3')
def solve(Rd3,sg):
    E1=sp.Eq(1, Om+(f0-R0-6*Rd1*f2)/6)                                      # (11.14), F'=1
    E2=sp.Eq(-Hd0, sp.Rational(3,2)*Om+(Rd1**2*f3+(Rd2-Rd1)*f2)/2)           # (11.15)
    E3=sp.Eq(Hdd0,(Rd1**2*f3+(Rd2-Rd1)*f2+3*Om)*Rd1*f2/2-(3*Rd1*Rd2-Rd1**2)*f3/2
             -((Rd3-Rd2+sg*Hd0*Rd1)*f2-9*Om)/2)                               # (11.20), F''''=0
    return sp.solve([E1,E2,E3],[f0,f2,f3],dict=True)
P0=(j-q-2)*l-(3*s+7*j+6*q**2+41*q+22)*s-((3*q+16)*j+20*q**2+64*q+12)*j-(3*q**4+25*q**3+96*q**2+72*q+20)
Q0=(q**2-j*q+2*q)*l+(3*q*s+(4*q+6)*j+6*q**3+44*q**2+22*q-12)*s+(2*j**2+(3*q**2+10*q-6)*j+17*q**3+52*q**2+54*q+36)*j+3*q**5+28*q**4+118*q**3+72*q**2-76*q-64
P2=9*s+6*j+9*q**2+66*q+42
Q2=-(6*(q+1)*s+(2*j-2*(1-q))*j+6*q**3+50*q**2+74*q+32)
P3=3*l+3*s-9*(q+4)*j-(45*q**2+78*q+12)
Q3=-(2*(1+q)*l+2*(j+q)*s-(2*j+4*q**2+12*q+6)*j-(30*q**3+84*q**2+78*q+24))
Rpr=(j-q-2)*l-(3*s-2*j+6*q**2+50*q+40)*s+((3*q+10)*j+11*q**2+4*q+18)*j-(3*q**4+34*q**3+246*q+104)
pf0=-6*(P0*Om+Q0)/Rpr; pf2=-(P2*Om+Q2)/Rpr/6; pf3=-(P3*Om+Q3)/((j-q-2)*Rpr)/36
for name,(Rd3,sg) in {'correct (11.13),(11.20)':(Rd3_true,-1),'printed (11.13) sign':(Rd3_print,-1),
                      'printed +HdotRdot':(Rd3_true,+1),'both printed':(Rd3_print,+1)}.items():
    sol=solve(Rd3,sg)[0]
    print(f"\n--- system with {name}")
    # compare numerators/denominator by matching ratios that do not involve R
    r2=sp.cancel(sp.together(sol[f2]/sol[f0]-pf2/pf0)); r3=sp.cancel(sp.together(sol[f3]/sol[f0]-pf3/pf0))
    print("  F''/F  derived - printed :", r2)
    print("  F'''/F derived - printed :", r3)
    if name.startswith('correct'):
        Rder=sp.factor(sp.denom(sp.factor(sol[f2])))
        Rcorr=sp.expand(-(sp.together(sol[f2]).as_numer_denom()[1])/6)
        # normalise: correct R such that f2 = -(P2 Om+Q2)/(6 R)
        Rcorr=sp.expand(sp.cancel(-(P2*Om+Q2)/(6*sol[f2])))
        print("  correct R (so that printed P2,Q2 hold) =",Rcorr)
        print("  printed R - correct R =",sp.factor(sp.expand(Rpr-Rcorr)))
        print("  check f0 with correct R:",sp.cancel(sol[f0]-(-6*(P0*Om+Q0)/Rcorr)))
        print("  check f3 with correct R:",sp.cancel(sol[f3]-(-(P3*Om+Q3)/((j-q-2)*Rcorr)/36)))
        SOL=sol; RCORR=Rcorr
# ---------- LCDM (11.39)-(11.40) ----------
L={q:sp.Rational(1,2)-sp.Rational(3,2)*(1-Om), j:1, s:1-sp.Rational(9,2)*Om, l:1+3*Om+sp.Rational(27,2)*Om**2}
Lam=3*(1-Om)  # Lambda = 3 H0^2 Omega_Lambda (kappa^2=1, rho_Lambda=Lambda)
print("\n--- LCDM (11.40): F(R0)=R0+2Lambda, F''=F'''=0")
print("  derived  f0 - (R0+2Lam):",sp.cancel(SOL[f0].subs(L)-(R0.subs(L)+2*Lam)),
      " f2:",sp.cancel(SOL[f2].subs(L))," f3:",sp.cancel(SOL[f3].subs(L)))
print("  printed (with printed R) f0 =",sp.factor(sp.cancel(pf0.subs(L))),
      "; expected R0+2Lam =",sp.expand(R0.subs(L)+2*Lam))
print("  printed f2, f3 at LCDM:",sp.cancel(pf2.subs(L)),sp.cancel(pf3.subs(L)))
print("  P2*Om+Q2 at LCDM:",sp.expand((P2*Om+Q2).subs(L)),"; P3*Om+Q3:",sp.expand((P3*Om+Q3).subs(L)))
print("  printed R at LCDM:",sp.factor(sp.expand(Rpr.subs(L))),"; correct R at LCDM:",sp.factor(sp.expand(RCORR.subs(L))))
# Only (q0,j0) fixed to LCDM, (s0,l0) free -> claim same result
Lqj={q:L[q], j:1}
print("  (q0,j0)=LCDM, s0,l0 free: f2 =",sp.cancel(SOL[f2].subs(Lqj)),", f3 =",sp.cancel(SOL[f3].subs(Lqj)),
      ", f0-(R0+2Lam) =",sp.cancel(SOL[f0].subs(Lqj)-(R0.subs(Lqj)+2*Lam)))
print("  same with printed R: f0-(R0+2Lam) =",sp.factor(sp.cancel(pf0.subs(Lqj)-(R0.subs(Lqj)+2*Lam))))
# ---------- CPL (11.35)-(11.38) ----------
E2=Om*(1+z)**3+(1-Om)*(1+z)**(3*(1+w0+wa))*sp.exp(-3*wa*z/(1+z))
Hz=sp.sqrt(E2)
def ddt(f): return -(1+z)*Hz*sp.diff(f,z)
d=[Hz]
for n in range(4): d.append(ddt(d[-1]))
vals=[sp.simplify(x.subs(z,0)) for x in d[1:]]
qq,jj,ss,ll=sp.symbols('qq jj ss ll')
eqs=[sp.Eq(vals[0],-(1+qq)),sp.Eq(vals[1],jj+3*qq+2),sp.Eq(vals[2],ss-4*jj-3*qq*(qq+4)-6),
     sp.Eq(vals[3],ll-5*ss+10*(qq+2)*jj+30*(qq+2)*qq+24)]
cs=sp.solve(eqs,[qq,jj,ss,ll],dict=True)[0]
q_pr=sp.Rational(1,2)+sp.Rational(3,2)*(1-Om)*w0
j_pr=1+sp.Rational(3,2)*(1-Om)*(3*w0*(1+w0)+wa)
s_pr=(-sp.Rational(7,2)-sp.Rational(33,4)*(1-Om)*wa-sp.Rational(9,4)*(1-Om)*(9+(7-Om)*wa)*w0
      -sp.Rational(9,4)*(1-Om)*(16-3*Om)*w0**2-sp.Rational(27,4)*(1-Om)*(3-Om)*w0**3)
l_pr=(sp.Rational(35,2)+(1-Om)/4*(213+(7-Om)*wa)*wa+(1-Om)/4*(489+9*(82-21*Om)*wa)*w0
      +sp.Rational(9,2)*(1-Om)*(67-21*Om+sp.Rational(3,2)*(23-11*Om)*wa)*w0**2
      +sp.Rational(27,4)*(1-Om)*(47-24*Om)*w0**3+sp.Rational(81,2)*(1-Om)*(3-2*Om)*w0**4)
print("\n--- CPL (11.35)-(11.38): printed - derived")
for nm,pv,key in (('q0',q_pr,qq),('j0',j_pr,jj),('s0',s_pr,ss),('l0',l_pr,ll)):
    print(" ",nm,":",sp.factor(sp.expand(pv-cs[key])))
print("  derived s0 =",sp.collect(sp.expand(cs[ss]),[w0,wa]))
print("  derived l0 =",sp.collect(sp.expand(cs[ll]),[w0,wa]))
print("  LCDM (w0,wa)=(-1,0) derived:",[sp.factor(sp.expand(cs[k].subs({w0:-1,wa:0}))) for k in (qq,jj,ss,ll)])
print("  (11.39) printed - derived:",[sp.expand(L[k]-cs[kk].subs({w0:-1,wa:0})) for k,kk in ((q,qq),(j,jj),(s,ss),(l,ll))])
# ---------- (11.42)-(11.45) ----------
Le={q:L[q]*(1+eps), j:(1+eps), s:L[s]*(1+eps), l:L[l]*(1+eps)}
eta20=sp.cancel((SOL[f2]/SOL[f0]).subs(Le))
eta30=sp.cancel((SOL[f3]/SOL[f0]).subs(Le))
e20=sp.factor(sp.cancel(sp.diff(eta20,eps).subs(eps,0)))
e30=sp.factor(sp.cancel(sp.diff(eta30,eps).subs(eps,0)))
D_=(3*(9*Om+74)*Om-556)*Om**2+16
p20=(64-6*Om*(9*Om+8))/D_/27
p30=(6*((81*Om-110)*Om+40)*Om+16)/D_/(243*Om**2)
print("\n--- (11.42)-(11.43) first-order coefficients")
print("  eta20/eps derived:",e20,"\n   printed-derived:",sp.cancel(p20-e20))
print("  eta30/eps derived:",e30,"\n   printed-derived:",sp.cancel(p30-e30))
for o in (0.041,0.25):
    print(f"  Om={o}: eta20/eps={float(e20.subs(Om,o)):.4f}, eta30/eps={float(e30.subs(Om,o)):.4f}")
# ---------- (11.46)-(11.47) ----------
jq=sp.factor(sp.expand((cs[jj]-cs[qq]-2).subs(wa,0)))
print("\n--- quiescence j0-q0-2 (wa=0) =",jq)
roots=sp.solve(jq,w0)
w1=1/(1-Om+sp.sqrt((1-Om)*(4-Om)))  # as printed? see crop
print("  roots:",[sp.cancel(r) for r in roots])
for o in (sp.Rational(41,1000),sp.Rational(1,4)):
    print("  Om=",o," numeric roots:",[sp.N(r.subs(Om,o)) for r in roots])
