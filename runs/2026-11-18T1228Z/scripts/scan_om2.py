exec(open('scan_om.py').read().split("# rl19 hyp 2")[0])
for O in [mpf(x) for x in [1.5,2,3,4,5,6,8,10,15,20]]:
    d=[dLf(O,Z) for Z in Zs]; best=None
    for a2 in fr(-3,8,110):
        for a3 in fr(-5,10,150):
            s=spread(d,xs,a2,a3)
            if s is None: continue
            v=viol(O,a2,a3)
            if v<=0: continue
            if best is None or s<best[0]: best=(s,v,a2,a3)
    print(float(O),[round(float(t),4) for t in best])
