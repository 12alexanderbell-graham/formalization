import sympy as sp
H,W,A=sp.symbols('H W A')
d=sp.symbols('d0:9')
def D(e): return sum(sp.diff(e,d[i])*d[i+1] for i in range(8))
E0=d[0]*d[1]**2 - H**2*(W*A**3+(1-W)*d[0]**3)
R=[sp.expand(sp.cancel(D(E0)/d[1]))]
assert sp.expand(D(E0)-d[1]*R[0])==0
for k in range(4): R.append(sp.expand(D(R[-1])))
def cstr(c):
    s=sp.sstr(sp.factor(c)).replace('**','^').replace('H','H₀').replace('W','Ω').replace('A','a₀')
    return '('+s+')'
def terms(e):
    P=sp.Poly(e,*d[:9])
    return P.terms()
def fn(e):  # function body string at variable t
    out=[]
    for mon,c in terms(e):
        fac=[f"D {i} t" + (f" ^ {p}" if p>1 else "") for i,p in enumerate(mon) if p>0]
        body=" * ".join(fac) if fac else None
        out.append(f"{cstr(c)} * ({body})" if body else cstr(c))
    # left nested sum
    s=out[0]
    for o in out[1:]: s=f"({s}) + ({o})"
    return s
def term(e):
    out=[]
    for mon,c in terms(e):
        fac=[(f"(h{i}.pow {p})" if p>1 else f"h{i}") for i,p in enumerate(mon) if p>0]
        if fac:
            t=fac[0]
            for f in fac[1:]: t=f"({t}.mul {f})"
            # match fn: D i t ^ p * D j t ... product left-assoc: a * b * c = (a*b)*c ok
            out.append(f"({t}.const_mul {cstr(c)})")
        else:
            out.append(f"(hasDerivAt_const t {cstr(c)})")
    s=out[0]
    for o in out[1:]: s=f"({s}.add {o})"
    return s
import json
res={'E':(fn(E0),term(E0)),'R':[(fn(r),term(r)) for r in R]}
# derivative values
res['dE']="D 1 t * ("+fn(R[0])+")"
# solve at t0
vals={d[0]:A, d[1]:H*A}
sol={}
for k,r in enumerate(R):
    x=d[k+2]
    v=sp.solve(r.subs(vals),x)[0]
    v=sp.factor(sp.expand(v))
    vals[x]=v
    print(f"d{k+2} =", v, " normalized:", sp.expand(v/(A*H**(k+2))))
json.dump({k:(v if isinstance(v,str) else v) for k,v in res.items()},open('gen.json','w'))
# linear_combination certificates: goal 2*A*(d_{k+2} - v) = 0 using hR_k : R_k(t0)=0 and he_j : d_j = v_j
cert=[]
for k,r in enumerate(R):
    x=d[k+2]; v=vals[x]
    lower=[j for j in range(1,k+2)]
    # S(D) = R_k - 2 A d_{k+2}  (with d0=A substituted)
    S=sp.expand(r.subs(d[0],A)-2*A*x)
    assert sp.expand(sp.diff(S,x))==0, "nonlinear"
    # telescoping: substitute lower one at a time from highest
    Q={}
    cur=S
    for j in reversed(lower):
        nxt=cur.subs(d[j],vals[d[j]])
        Q[j]=sp.factor(sp.cancel((cur-nxt)/(d[j]-vals[d[j]])))
        cur=sp.expand(nxt)
    assert sp.expand(cur+2*A*v)==0
    cert.append(Q)
    print(k, {j:str(q) for j,q in Q.items()})
import pickle; pickle.dump((R,vals,cert),open('gen.pkl','wb'))
