import sympy as sp
x,q,j,s,l=sp.symbols('x q j s l')
def trunc(p,n=5): p=sp.expand(p); return sum(p.coeff(x,k)*x**k for k in range(n+1))
def high(p,n=5): p=sp.expand(p); return sp.expand(sum(p.coeff(x,k)*x**(k-6) for k in range(n+1, sp.Poly(p,x).degree()+1)))
A = 1 - x - q/2*x**2 - j/6*x**3 + s/24*x**4 - l/120*x**5
B = trunc(sp.series(1/A,x,0,6).removeO())
C0 = high(A*B); assert sp.expand(A*B - 1 - x**6*C0)==0
Z = sp.expand(B-1); Zs=[None,Z]
W=[None]
for k in range(1,5):
    P = sp.expand(Z*Zs[k]); Zs.append(trunc(P)); W.append(high(P)); assert sp.expand(P-Zs[k+1]-x**6*W[k])==0
D1=-(1+q/2); D2=1+q+q**2/2-j/6
D3=-(1+sp.Rational(3,2)*q+sp.Rational(3,2)*q**2+sp.Rational(5,8)*q**3-j/2-sp.Rational(5,12)*q*j-s/24)
D4=1+2*q+3*q**2+sp.Rational(5,2)*q**3+sp.Rational(7,8)*q**4-sp.Rational(5,3)*q*j-sp.Rational(7,8)*q**2*j-j+j**2/12-q*s/8-s/6-l/120
print('final', sp.expand(Zs[1]+D1*Zs[2]+D2*Zs[3]+D3*Zs[4]+D4*Zs[5]-x))
def L(p): return str(sp.expand(p)).replace('**','^')
print('B :=', L(B)); print('C0 :=', L(C0))
for k in range(1,6): print(f'Z{k} :=', L(Zs[k]))
for k in range(1,5): print(f'W{k} :=', L(W[k]), len(sp.expand(W[k]).args))
out=[]
def defn(name, p, doc):
    out.append(f'/-- {doc} -/\nnoncomputable def {name} (q j s l x : ℝ) : ℝ :=\n  {L(p)}\n')
defn('Apoly', A, 'Fifth-order Taylor polynomial of `a/a₀` in `x = H₀ (t₀ − t)` (Eq. (A1)).')
defn('Bpoly', B, 'Degree-5 truncation of `1/A`.')
defn('C0poly', C0, '`A B = 1 + x⁶ C0`.')
for k in range(1,6): defn(f'Zp{k}', Zs[k], f'Degree-5 truncation of `(B − 1)^{k}`.')
for k in range(1,5): defn(f'Wp{k}', W[k], f'`Z1 Z{k} = Z{k+1} + x⁶ W{k}`.')
open('/tmp/claude-0/c3/polys.lean','w').write('\n'.join(out))
