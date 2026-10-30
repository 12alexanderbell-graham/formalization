import sympy as sp, pickle
exec(open('gen.py').read().split("import json")[0])
R,vals,_=pickle.load(open('gen.pkl','rb'))
x0=sp.Symbol('x')
def lean(c):
    s=sp.sstr(c).replace('**','^').replace('H','H₀').replace('W','Ω').replace('A','a₀')
    for i in range(9): s=s.replace(f'd{i}',f'D {i} t₀')
    return '('+s+')'
L=[]
L.append("    -- E and its derivative")
fE,tE=fn(E0),term(E0)
L.append(f"  have dE : ∀ᶠ t in 𝓝 t₀, HasDerivAt (fun t => {fE}) (D 1 t * ({fn(R[0])})) t := by")
L.append(f"    filter_upwards [hder] with t ⟨h0, h1, h2, h3, h4, h5⟩")
L.append(f"    exact ({tE}).congr_deriv (by push_cast; ring)")
for k in range(4):
    L.append(f"  have dR{k} : ∀ᶠ t in 𝓝 t₀, HasDerivAt (fun t => {fn(R[k])}) ({fn(R[k+1])}) t := by")
    L.append(f"    filter_upwards [hder] with t ⟨h0, h1, h2, h3, h4, h5⟩")
    L.append(f"    exact ({term(R[k])}).congr_deriv (by push_cast; ring)")
# certificates
for k,r in enumerate(R):
    x=d[k+2]; v=vals[x]
    goal=2*A*(x-v)
    rest=sp.expand(goal-r)
    cs={}
    cur=rest
    for j in reversed(range(0,k+2)):
        nxt=cur.subs(d[j],vals[d[j]])
        cs[j]=sp.factor(sp.cancel((cur-nxt)/(d[j]-vals[d[j]])))
        cur=sp.expand(nxt)
    assert sp.expand(cur)==0
    chk=sp.expand(goal - r - sum(cs[j]*(d[j]-vals[d[j]]) for j in cs))
    assert chk==0, chk
    lc=" + ".join(f"{lean(cs[j])} * he{j}" for j in sorted(cs))
    L.append(f"  have e{k+2} : D {k+2} t₀ = {lean(v)} := by")
    L.append(f"    have : 2 * a₀ * (D {k+2} t₀ - {lean(v)}) = 0 := by linear_combination hR{k} + {lc}")
    L.append(f"    rcases mul_eq_zero.1 this with h | h")
    L.append(f"    · exact absurd h (by positivity)")
    L.append(f"    · linarith")
    L.append(f"  have he{k+2} := e{k+2}")
open('proof_parts.lean','w').write("\n".join(L))
# R_k at t0 statements
S=[]
S.append(f"  have hR0' : ∀ᶠ t in 𝓝 t₀, {fn(R[0])} = 0 := ?R0")
for k in range(4):
    S.append(f"  have hR{k+1}' := step hR{k}' dR{k}")
for k in range(5):
    S.append(f"  have hR{k} := hR{k}'.self_of_nhds")
open('rparts.lean','w').write("\n".join(S))
print(fE)
