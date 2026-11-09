# Symbolic checks of the identities in fs_negative_beta.md
import sympy as sp
eta=sp.symbols('eta'); K,mu,M=sp.symbols('K mu M',positive=True)
f=sp.Function('f')(eta); p=sp.Function('p')(eta); q=sp.Function('q')(eta)
rules={f.diff(eta):p, p.diff(eta):q, q.diff(eta):-K*f*q+1-p**2}
D=lambda e: sp.expand(e.diff(eta).subs(rules))
g=1-p
# Lemma I
W=q-mu*g
claimI=(mu-K*f)*W+g*(mu**2-mu*K*f+2-g)
print('Lemma I  W\' identity :', sp.simplify(D(W)-sp.expand(claimI))==0)
th=(mu+2/mu)/K
print('Lemma I  bracket at f=theta, g=0:', sp.simplify(mu**2-mu*K*th+2))
# Lemma R
r=q/g
claimR=r**2-K*f*r+2-g
print('Lemma R  r\' identity :', sp.simplify(D(r)-claimR)==0)
# Lemma R inequalities: at r=M, r' <= M(M-Kf)+2 ; with Kf>=M+3/mu, M>=mu
x=sp.symbols('x',positive=True)  # x = Kf-(M+3/mu) >= 0
print('Lemma R  M(M-Kf)+2 with Kf=M+3/mu+x :', sp.simplify(M*(M-(M+3/mu+x))+2), '  (<= -1 iff 3M/mu>=3, i.e. M>=mu)')
# Lemma T: D' at crossing; U' Step 1
t=sp.symbols('t'); z1,z2,F1,F2,E0=sp.symbols('z1 z2 F1 F2 E0')
dz=lambda F,z: -K*F+(1-t**2)/z
Dp=dz(F2,z2)-dz(F1,z1)
print('Lemma T  D\' - [K E + (1-t^2)(1/z2-1/z1)] :', sp.simplify(Dp-(K*(F1-F2)+(1-t**2)*(1/z2-1/z1))))
print('Lemma T  D\' at z1=z2 :', sp.simplify(Dp.subs(z2,z1)))
G1p=1/z1-t/z1
Psip=Dp+2*G1p-K*E0
claim=K*((F1-F2)-E0)+(1-t)**2/z1+(1-t**2)/z2
print('U\' Step1 Psi\' - [K(E-E0)+(1-t)^2/z1+(1-t^2)/z2] :', sp.simplify(Psip-claim))
# U' Step 2: chi' = 1-p-q/M
chi=eta-f-p/M
print('U\' Step2 chi\' :', D(chi))
# Lemma D
fm,pm,qm=sp.symbols('fm pm qm'); fy,py,qy=sp.symbols('fy py qy')
rhs=lambda F,P,Q: -K*F*Q+1-P**2
dq=rhs(fy,py,qy)-rhs(fm,pm,qm)
claimD=-K*qy*(fy-fm)-K*fm*(qy-qm)-(py+pm)*(py-pm)
print('Lemma D  Delta q\' identity :', sp.simplify(dq-claimD)==0)
# Lemma L: phi' where phi = q - c/(2K(B+eta))
c,B=sp.symbols('c B',positive=True)
print('Lemma L  d/deta[-c/(2K(B+eta))] =', sp.diff(-c/(2*K*(B+eta)),eta))
# Lyapunov H for clamp bounds (fix proposal)
H=q**2/2+p**3/3-p
print('Energy   H\' =', sp.factor(D(H)))
# Scaling check: F(s)=c f(s/c) solves F'''=-F F''/c^2+(1-F'^2) if f'''=-f f''+|b|(1-f'^2), c=sqrt|b|
s,b=sp.symbols('s b',positive=True); cc=sp.sqrt(b)
ff=sp.Function('ff')
Fs=cc*ff(s/cc)
lhs=Fs.diff(s,3)
target=-Fs*Fs.diff(s,2)/cc**2+(1-Fs.diff(s)**2)
u=sp.symbols('u')
expr=(lhs-target)
# substitute f'''(u) = -f f'' + b(1-f'^2) at u=s/c
f3=sp.Subs(sp.Derivative(ff(u),(u,3)),u,s/cc)
e2=expr.doit()
e2=e2.replace(lambda e: isinstance(e,sp.Subs) and e.args[0]==sp.Derivative(ff(u),(u,3)),
              lambda e: (-ff(u)*sp.Derivative(ff(u),(u,2))+b*(1-sp.Derivative(ff(u),u)**2)).subs(u,s/cc))
print('Scaling residual :', sp.simplify(e2.doit()))
