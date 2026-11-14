import subprocess,sys,re
root=sys.argv[1]; base=sys.argv[2]
yml=open(root+"/.github/workflows/lean.yml").read()
def block(name):
    lines=yml.splitlines()
    s=next(i for i,l in enumerate(lines) if l.strip().startswith(name))
    r=next(i for i in range(s,len(lines)) if lines[i].strip()=="run: |")
    ind=len(lines[r+1])-len(lines[r+1].lstrip()); out=[]
    for l in lines[r+1:]:
        if l.strip() and len(l)-len(l.lstrip())<ind: break
        out.append(l.strip())
    return [c for c in out if c and not c.startswith("#") and c.startswith("python3")]
cmds=block("- name: Statement dependencies")+block("- name: Frozen statements")
bad=[]
def run(c):
    return subprocess.run(c.replace('"$BASE"',base),shell=True,cwd=root,capture_output=True,text=True)
# regenerate as author
for c in ["python3 scripts/trust/check_numbers.py --write","python3 validation/make_packet.py"]:
    r=run(c); print("GEN",c,r.returncode)
for c in cmds:
    r=run(c)
    if r.returncode: 
        bad.append(c); print("FAIL",c); print((r.stdout+r.stderr)[-1500:])
print("done",len(cmds),"cmds",len(bad),"failed")
