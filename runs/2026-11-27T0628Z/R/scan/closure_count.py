import os,re,sys
os.chdir(sys.argv[1])
seen=set();ext=set();stack=['Main']
lines=0
while stack:
    m=stack.pop()
    if m in seen: continue
    p=m.replace('.','/')+'.lean'
    if not os.path.exists(p): ext.add(m.split('.')[0]); continue
    seen.add(m)
    for line in open(p,encoding='utf-8'):
        lines+=1
        mm=re.match(r'\s*(?:public\s+)?(?:meta\s+)?import\s+(.*)',line)
        if mm: stack.extend(mm.group(1).split())
print(len(seen),'modules',lines,'lines',sorted(ext))
