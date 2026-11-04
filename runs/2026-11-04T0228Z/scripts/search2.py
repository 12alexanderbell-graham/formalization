from gen_fit import *
import sys, pickle
N = int(sys.argv[1]); DEPTH=int(sys.argv[2])
PAIRS = [[(3,1),(3,5)], [(1,5),(3,5)], [(1,3),(1,5)], [(3,1),(1,5)]]
def cover(A_,B_,low,upp):
    cases=[]; stack=[(A_,B_,0)]
    while stack:
        a_,b_,d=stack.pop()
        best=None
        for pr in PAIRS:
            r=try_case(a_,b_,pr,low,upp)
            if r and (best is None or r['min']>best['min']): best=r
        if best and best['ok']: cases.append(best)
        elif d>=DEPTH: return None
        else:
            m=(a_+b_)/2; stack += [(m,b_,d+1),(a_,m,d+1)]
    return cases
def jint(A_,B_):
    mid=(A_+B_)/2
    low={j:lower_cert(j,mid,N) for j in (1,3,5)}
    upp={k:upper_cert(k,A_,B_,N) for k in (1,3)}
    cs=cover(A_,B_,low,upp)
    if cs is not None: return [((A_,B_),low,upp,cs)]
    m=(A_+B_)/2
    return jint(A_,m)+jint(m,B_)
res=jint(F(0),F(1))
print("Jints",len(res),"cases",sum(len(r[3]) for r in res))
for (iv,low,upp,cs) in res: print(float(iv[0]),float(iv[1]),len(cs), sorted(set(tuple((c[0],c[1]) for c in x['cons']) for x in cs)), round(float(min(x['min']-M for x in cs)),4))
pickle.dump(res,open(f'/tmp/claude-0/res_{N}_{DEPTH}.pkl','wb'))
