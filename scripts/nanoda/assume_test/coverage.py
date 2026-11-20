#!/usr/bin/env python3
# Coverage check of the assumed-theorem export (run 2026-11-20T1428Z; used by run_init_test.sh in its work dir):
# reads old<i>.txt / new<i>.txt (lean4export NDJSON) and assumed<i>.txt for i = 0..3.
import json,sys
def load(f):
    names={0:''}; decl={}
    for l in open(f):
        o=json.loads(l)
        if 'in' in o:
            if 'str' in o: names[o['in']]=(names[o['str']['pre']]+'.' if names[o['str']['pre']] else '')+o['str']['str']
            else: names[o['in']]=(names[o['num']['pre']]+'.' if names[o['num']['pre']] else '')+str(o['num']['i'])
        for k in ('thm','def','axiom','opaque'):
            if k in o: decl[names[o[k]['name']]]=k
        if 'inductive' in o:
            for t in o['inductive']['types']: decl[names[t['name']]]='ind'
    return decl
old=[load(f'old{i}.txt') for i in range(4)]; new=[load(f'new{i}.txt') for i in range(4)]
oldfull=set().union(*[{n for n,k in d.items() if k!='axiom'} for d in old])
newfull=set().union(*[{n for n,k in d.items() if k!='axiom'} for d in new])
print('full decls old union',len(oldfull),'new union',len(newfull),'missing from new',len(oldfull-newfull), 'extra', len(newfull-oldfull))
for i in range(4):
    a=[l.strip() for l in open(f'assumed{i}.txt') if l.strip()]
    bad=[x for x in a if not any(new[j].get(x)=='thm' for j in range(4) if j!=i)]
    print('shard',i,'assumed',len(a),'not fully checked elsewhere',len(bad), 'decls old',len(old[i]),'new',len(new[i]))
