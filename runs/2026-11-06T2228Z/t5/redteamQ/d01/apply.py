import sys, pathlib
root = pathlib.Path(sys.argv[1])
def rd(p): return (root/p).read_text(encoding="utf-8")
def wr(p, s): (root/p).write_text(s, encoding="utf-8")
def app(p, s):
    t = rd(p)
    if not t.endswith("\n"): t += "\n"
    wr(p, t + s)
def rep(p, old, new):
    t = rd(p); assert t.count(old) == 1, (p, old[:60], t.count(old)); wr(p, t.replace(old, new))
rep("STATE.md", '- **PROVED in Work + AUDITED** (part 5 mathematics, run 2026-11-06T1628Z; local build, axioms standard; CI of 1757139 and 03bbb04: next run) `Work.Math.GelfandPDE.gelfand_pde_radial_bound`', '- **Machine-checked, promoted to Checked and AUDITED** (part 5 mathematics, run 2026-11-06T2328Z; promotion CI green on every job, nanoda and leanchecker included) `Work.Math.GelfandPDE.gelfand_pde_radial_bound`')
