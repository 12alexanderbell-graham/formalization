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
LEAN="import Checked.Records.Basic\nimport Checked.Cosmography.LCDMCoefficients\n\nnamespace Checked.Cosmography.Aviles\n\nopen Checked.Records\n\n/-- There is a density `Ω` rounding to `0.3` such that every flat LCDM scale factor with `a t₀ = 0` has `decel a t₀ = 1 / 2`. -/\ntheorem decel_half_when_scale_vanishes :\n    ∃ Ω : ℝ, RoundsTo Ω 0.3 1 ∧\n      ∀ (a : ℝ → ℝ) (t₀ : ℝ), IsFlatLCDM Ω a t₀ → a t₀ = 0 → decel a t₀ = 1 / 2 := by\n  refine ⟨3 / 10, ?_, fun a t₀ hL h0 => ?_⟩\n  · unfold RoundsTo\n    rw [abs_le]\n    norm_num\n  · exfalso\n    obtain ⟨-, hev⟩ := hL\n    exact (hev.self_of_nhds.1).ne' h0\n\nend Checked.Cosmography.Aviles\n"
wr('Checked/Cosmography/AvilesVanishing.lean',LEAN)
app('Checked.lean','import Checked.Cosmography.AvilesVanishing')
app('scripts/trust/headlines.txt','Checked.Cosmography.Aviles.decel_half_when_scale_vanishes')
