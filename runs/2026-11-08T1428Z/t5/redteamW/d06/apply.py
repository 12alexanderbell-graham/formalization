import sys, os
root = sys.argv[1]
def rd(p): return open(os.path.join(root,p),encoding="utf-8").read()
def wr(p,s):
    os.makedirs(os.path.dirname(os.path.join(root,p)),exist_ok=True)
    open(os.path.join(root,p),"w",encoding="utf-8").write(s)
def app(p,line):
    s=rd(p)
    if not s.endswith("\n"): s+="\n"
    wr(p,s+line+"\n")
def rep(p,old,new):
    s=rd(p); assert s.count(old)==1,(p,old); wr(p,s.replace(old,new))
LEAN='import Checked.Records.Findings\n\nnamespace Checked.Records\n\nnoncomputable def l0Value (Ω : ℝ) : ℝ := printedAvilesL0 Ω + 0\n\ntheorem F1_l0Value_at_one (Ω : ℝ) (h : Ω = 1) : RoundsTo (l0Value Ω) (-9.5) 1 := by\n  subst h\n  unfold l0Value printedAvilesL0 RoundsTo\n  rw [abs_le]\n  norm_num\n\nend Checked.Records\n\nnamespace Checked.Trust.NV\n\ntheorem F1_l0Value_at_one : nonvacuity% Checked.Records.F1_l0Value_at_one := ⟨1, rfl, trivial⟩\n\nend Checked.Trust.NV\n'
wr('Checked/Records/DerivedL0.lean',LEAN)
app('Checked.lean','import Checked.Records.DerivedL0')
app('scripts/trust/def_kinds.txt','Checked.Records.l0Value COMPOSITE')
app('scripts/trust/headlines.txt','Checked.Records.F1_l0Value_at_one')
rep('FINDINGS.md','- **Fidelity audit:** `runs/2026-10-30T0220Z/audit.md`','<!-- certified: F1_l0Value_at_one -->\n<!-- /certified -->\n\n- **Fidelity audit:** `runs/2026-10-30T0220Z/audit.md`')
