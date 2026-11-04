from gen_fit import *
import sys
N = int(sys.argv[1]); W = F(sys.argv[2])  # J-interval width
PAIRS = [[(3,1),(3,5)], [(1,5),(3,5)], [(1,3),(1,5)], [(3,1),(1,5)]]
def run():
    cases=[]; Jints=[]
    a=F(0)
    while a < 1:
        b=min(a+W,F(1)); Jints.append((a,b)); a=b
    certs={}
    for (A_,B_) in Jints:
        mid=(A_+B_)/2
        low={j:lower_cert(j,mid,N) for j in (1,3,5)}
        upp={k:upper_cert(k,A_,B_,N) for k in (1,3)}
        certs[(A_,B_)]=(low,upp)
        stack=[(A_,B_)]
        while stack:
            a_,b_=stack.pop()
            best=None
            for pr in PAIRS:
                r=try_case(a_,b_,pr,low,upp)
                if r and (best is None or r['min']>best['min']): best=r
            if best and best['ok']: cases.append(best)
            else:
                if b_-a_ < F(1,2000): print("FAIL",float(a_),float(b_), best and float(best['min'])); return None
                m=(a_+b_)/2; stack += [(m,b_),(a_,m)]
    return cases,certs
out=run()
if out:
    cases,certs=out
    print("cases",len(cases),"Jints",len(certs))
    print(sorted(set(tuple((c[0],c[1]) for c in x['cons']) for x in cases)))
    print("min slack", float(min(x['min']-M for x in cases)))
