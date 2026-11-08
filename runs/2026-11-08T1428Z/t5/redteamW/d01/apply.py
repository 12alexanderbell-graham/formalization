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
LEAN='import Checked.Cosmography.Lookback\nimport Checked.Trust.NonVacuity\n\nnamespace Checked.Cosmography\n\n/-- `decel a t₀ = 0` when `deriv a t₀ = 0`. -/\ntheorem decel_eq_zero_of_deriv_eq_zero (a : ℝ → ℝ) (t₀ : ℝ) (h : deriv a t₀ = 0) :\n    decel a t₀ = 0 := by\n  unfold decel\n  rw [h]\n  simp\n\nend Checked.Cosmography\n\nnamespace Checked.Trust.NV\n\ntheorem decel_eq_zero_of_deriv_eq_zero :\n    nonvacuity% Checked.Cosmography.decel_eq_zero_of_deriv_eq_zero :=\n  ⟨fun _ => 0, 0, by simp, trivial⟩\n\nend Checked.Trust.NV\n'
wr('Checked/Cosmography/TurningPoint.lean',LEAN)
app('Checked.lean','import Checked.Cosmography.TurningPoint')
app('scripts/trust/headlines.txt','Checked.Cosmography.decel_eq_zero_of_deriv_eq_zero')
