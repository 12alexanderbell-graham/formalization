#!/usr/bin/env python3
# Run 2026-11-20T1428Z: split each nanoda profile shard's per-module worker seconds into modules of the shard itself and
# modules of other shards (scripts/nanoda/shard_assignment.txt, else FNV-1a as ShardMain). Usage: own_vs_foreign.py <dir with a<i>/shard<i>.txt>
import sys
D=sys.argv[1]
asg={}
for l in open('scripts/nanoda/shard_assignment.txt'):
    l=l.strip()
    if not l or l.startswith('#'): continue
    a,b=l.split(); asg[a]=int(b)
def fnv(m,k):
    h=14695981039346656037
    for c in m:
        h=((h^ord(c))*1099511628211)&0xFFFFFFFFFFFFFFFF
    return h%k
def sh(m): return asg[m]%4 if m in asg else fnv(m,4)
for i in [0,2,3]:
    own=foreign=0; fc={}
    for l in open(f'{D}/shard{i}.txt'):
        t,n,m=l.split()[:3]; t=float(t)
        if sh(m)==i: own+=t
        else:
            foreign+=t
            top=m.split('.')[0]; fc[top]=fc.get(top,0)+t
    print(i,'own %.0f foreign %.0f'%(own,foreign), {k:round(v) for k,v in sorted(fc.items(),key=lambda x:-x[1])[:5]})
