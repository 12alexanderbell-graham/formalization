import re,sys,os,shutil
src,dst=sys.argv[1],sys.argv[2]
seen=set()
def deps(mod):
    if mod in seen: return
    p=os.path.join(src,mod.replace('.','/')+'.lean')
    if not os.path.exists(p): return
    seen.add(mod)
    for line in open(p):
        m=re.match(r'\s*(?:public\s+)?(?:meta\s+)?import\s+(.*)',line)
        if m:
            for x in m.group(1).split(): deps(x)
for m in sys.argv[3:]: deps(m)
for mod in seen:
    rel=mod.replace('.','/')+'.lean'
    os.makedirs(os.path.dirname(os.path.join(dst,rel)),exist_ok=True)
    shutil.copy(os.path.join(src,rel),os.path.join(dst,rel))
print(len(seen),'files copied')
