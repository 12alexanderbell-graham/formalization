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
LEAN='import Checked.Fidelity.MoreSpecs\nimport Checked.Trust.NonVacuity\n\nnamespace Checked.Cosmography\n\n/-- `0 < hubble a t`. -/\ndef IsAccelerating (a : ℝ → ℝ) (t : ℝ) : Prop := 0 < hubble a t\n\ntheorem powerLaw_isAccelerating (n t : ℝ) (hn : 0 < n) (ht : 0 < t) :\n    IsAccelerating (fun s => s ^ n) t := by\n  unfold IsAccelerating\n  rw [(Checked.Fidelity.hubble_meets_spec).powerLaw n t ht]\n  exact div_pos hn ht\n\nend Checked.Cosmography\n\nnamespace Checked.Trust.NV\n\ntheorem powerLaw_isAccelerating :\n    nonvacuity% Checked.Cosmography.powerLaw_isAccelerating :=\n  ⟨1, 1, one_pos, one_pos, trivial⟩\n\nend Checked.Trust.NV\n'
wr('Checked/Cosmography/AccelPredicate.lean',LEAN)
app('Checked.lean','import Checked.Cosmography.AccelPredicate')
app('scripts/trust/def_kinds.txt','Checked.Cosmography.IsAccelerating COMPOSITE')
app('scripts/trust/headlines.txt','Checked.Cosmography.powerLaw_isAccelerating')
