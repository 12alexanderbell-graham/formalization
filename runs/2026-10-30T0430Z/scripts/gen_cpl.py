# Generator for the C4 Lean proof (system of two eventually-zero polynomials).
# D_i = deriv^[i] a, G_i = deriv^[i] g, g = (a0/a)^p * exp(-3 wa (1 - a/a0)).
# E0 = a adot^2 - H^2 (W A^3 + (1-W) a^3 g)          (squared Friedmann law times a^3)
# E1 = A a gdot + P A g adot - 3 K a g adot          (chain rule for g)
import sympy as sp, sys
H,W,A,P,K=sp.symbols('H W A P K')
N=6
d=sp.symbols('d0:%d'%(N+1)); g=sp.symbols('g0:%d'%(N+1))
def Dt(e): return sp.expand(sum(sp.diff(e,d[i])*d[i+1]+sp.diff(e,g[i])*g[i+1] for i in range(N)))
E0=sp.expand(d[0]*d[1]**2-H**2*(W*A**3+(1-W)*d[0]**3*g[0]))
E1=sp.expand(A*d[0]*g[1]+P*A*g[0]*d[1]-3*K*d[0]*g[0]*d[1])
F0=[E0]; F1=[E1]
for k in range(4): F0.append(Dt(F0[-1]))
for k in range(3): F1.append(Dt(F1[-1]))
VARS=list(d)+list(g)
def name(v):
    s=str(v); return f"D {s[1:]}" if s[0]=='d' else f"G {s[1:]}"
def cstr(c):
    s=sp.sstr(sp.factor(c)).replace('**','^').replace('H','H₀').replace('W','Ω').replace('A','a₀').replace('P','p').replace('K','wₐ')
    return '('+s+')'
def terms(e):
    return sp.Poly(e,*VARS).terms()
def fn(e,t='t'):
    out=[]
    for mon,c in terms(e):
        fac=[f"{name(VARS[i])} {t}"+(f" ^ {p}" if p>1 else "") for i,p in enumerate(mon) if p>0]
        out.append(f"{cstr(c)} * ({' * '.join(fac)})" if fac else cstr(c))
    s=out[0]
    for o in out[1:]: s=f"({s}) + ({o})"
    return s
def hname(v):
    s=str(v); return f"hd{s[1:]}" if s[0]=='d' else f"hg{s[1:]}"
def term(e):
    out=[]
    for mon,c in terms(e):
        fac=[(f"({hname(VARS[i])}.pow {p})" if p>1 else hname(VARS[i])) for i,p in enumerate(mon) if p>0]
        if fac:
            t=fac[0]
            for f in fac[1:]: t=f"({t}.mul {f})"
            out.append(f"({t}.const_mul {cstr(c)})")
        else: out.append(f"(hasDerivAt_const t {cstr(c)})")
    s=out[0]
    for o in out[1:]: s=f"({s}.add {o})"
    return s
L=[]
HD="⟨hd0, hd1, hd2, hd3, hd4, hg0, hg1, hg2, hg3⟩"
def deriv_block(nm,F,kmax):
    for k in range(kmax):
        L.append(f"  have d{nm}_{k} : ∀ᶠ t in 𝓝 t₀, HasDerivAt (fun t => {fn(F[k])}) ({fn(F[k+1])}) t := by")
        L.append(f"    filter_upwards [hder] with t {HD}")
        L.append(f"    exact ({term(F[k])}).congr_deriv (by (try simp only [Pi.pow_apply, Pi.mul_apply]); push_cast; ring)")
# zero facts: hF0_0 from model (proved by hand, stated in this form), others by step
L.append("  -- GENERATED: zero functions")
L.append(f"  have hF0_0 : ∀ᶠ t in 𝓝 t₀, {fn(F0[0])} = 0 := by")
L.append("    filter_upwards [hE0] with t h"); L.append("    simp only [hD, hG, Function.iterate_zero, Function.iterate_one, id]"); L.append("    linear_combination h")
L.append(f"  have hF1_0 : ∀ᶠ t in 𝓝 t₀, {fn(F1[0])} = 0 := by")
L.append("    filter_upwards [hE1] with t h"); L.append("    simp only [hD, hG, Function.iterate_zero, Function.iterate_one, id]"); L.append("    linear_combination h")
deriv_block('F0',F0,4); deriv_block('F1',F1,3)
for k in range(1,5): L.append(f"  have hF0_{k} := step hF0_{k-1} dF0_{k-1}")
for k in range(1,4): L.append(f"  have hF1_{k} := step hF1_{k-1} dF1_{k-1}")
for k in range(5): L.append(f"  have z0_{k} := hF0_{k}.self_of_nhds")
for k in range(4): L.append(f"  have z1_{k} := hF1_{k}.self_of_nhds")
# solve
vals={d[0]:A,d[1]:H*A,g[0]:1}
known=[d[0],d[1],g[0]]
hyp={d[0]:'he_d0',d[1]:'he_d1',g[0]:'he_g0'}
order=[]
for k in range(4):
    order.append((g[k+1],F1[k],f"z1_{k}",A*A))
    order.append((d[k+2],F0[k+1],f"z0_{k+1}",2*A*A*H))
for (X,F,zn,lead) in order:
    F=sp.expand(F)
    assert sp.expand(sp.diff(F,X).subs(vals))==sp.expand(lead), (X, sp.diff(F,X).subs(vals))
    v=sp.factor(sp.solve(F.subs(vals),X)[0])
    Q={}; cur=F
    for j in reversed(known):
        nxt=sp.expand(cur.subs(j,vals[j]))
        Q[j]=sp.factor(sp.cancel((cur-nxt)/(j-vals[j]))); cur=nxt
    assert sp.expand(cur-lead*(X-v))==0
    cert=f"{zn}"+"".join(f" - ({sp.sstr(sp.expand(Q[j])).replace('**','^')}) * {hyp[j]}" for j in known if Q[j]!=0)
    # translate symbols in cert
    def tr(s):
        import re
        s=re.sub(r'\bd(\d)\b',lambda m:f"D {m.group(1)} t₀",s)
        s=re.sub(r'\bg(\d)\b',lambda m:f"G {m.group(1)} t₀",s)
        return s.replace('H','H₀').replace('W','Ω').replace('A','a₀').replace('P','p').replace('K','wₐ')
    vs=tr(sp.sstr(v).replace('**','^'))
    nmX=name(X)+" t₀"; leads=tr(sp.sstr(lead).replace('**','^'))
    hn=f"he_{str(X)}"
    L.append(f"  have {hn} : {nmX} = {vs} := by")
    L.append(f"    have h : ({leads}) * ({nmX} - ({vs})) = 0 := by")
    L.append(f"      linear_combination {tr(cert)}")
    L.append(f"    have hl : ({leads}) ≠ 0 := by positivity")
    L.append(f"    exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hl)")
    vals[X]=v; known.append(X); hyp[X]=hn
    print(X,'=',v, file=sys.stderr)
open('gen_cpl.lean.txt','w').write("\n".join(L)+"\n")
# final check of normalised values
w0=sp.symbols('w0')
sub={P:3*(1+w0+K)}
for k in range(2,6): print(k, sp.factor(sp.expand((vals[d[k]]/(A*H**k)).subs(sub))), file=sys.stderr)
