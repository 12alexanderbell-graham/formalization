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
LEAN='import Checked.Cosmography.BambaCurved\nimport Checked.Trust.NonVacuity\n\nnamespace Checked.Cosmography.BambaK\n\nopen Checked.Cosmography.BambaY Checked.Cosmography.Transverse\n\n/-- `lumDist K a t₀ t = lumDistFlat a t₀ t` when `K = 0`. -/\ntheorem lumDist_eq_lumDistFlat (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) (hK : K = 0) :\n    lumDist K a t₀ t = lumDistFlat a t₀ t := by\n  subst hK\n  simp [lumDist, lumDistFlat, transverse]\n\nend Checked.Cosmography.BambaK\n\nnamespace Checked.Trust.NV\n\ntheorem lumDist_eq_lumDistFlat :\n    nonvacuity% Checked.Cosmography.BambaK.lumDist_eq_lumDistFlat :=\n  ⟨0, fun _ => 1, 0, 0, rfl, trivial⟩\n\nend Checked.Trust.NV\n'
wr('Checked/Cosmography/FlatLimit.lean',LEAN)
app('Checked.lean','import Checked.Cosmography.FlatLimit')
app('scripts/trust/headlines.txt','Checked.Cosmography.BambaK.lumDist_eq_lumDistFlat')
