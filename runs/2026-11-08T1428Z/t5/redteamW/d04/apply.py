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
LEAN='import Checked.Fidelity.Pins\nimport Checked.Trust.NonVacuity\n\nnamespace Checked.Cosmography\n\n/-- `|hubble a t|`. -/\nnoncomputable def expansionRate (a : ℝ → ℝ) (t : ℝ) : ℝ := |hubble a t|\n\ntheorem expansionRate_timeReverse (a : ℝ → ℝ) (t : ℝ) :\n    expansionRate (fun s => a (-s)) t = expansionRate a (-t) := by\n  unfold expansionRate hubble\n  rw [deriv_comp_neg, neg_div, abs_neg]\n\nopen Checked.Fidelity in\ntheorem expansionRate_pins (H : (ℝ → ℝ) → ℝ → ℝ) (h : HubbleSpec H) (a : ℝ → ℝ) (t : ℝ)\n    (ha : 0 < a t) (hd : DifferentiableAt ℝ a t) (hp : 0 ≤ deriv a t) :\n    H a t = expansionRate a t := by\n  rw [hubbleSpec_pins H h a t ha hd]\n  unfold expansionRate hubble\n  exact (abs_of_nonneg (div_nonneg hp ha.le)).symm\n\nend Checked.Cosmography\n\nnamespace Checked.Trust.NV\n\ntheorem expansionRate_pins :\n    nonvacuity% Checked.Cosmography.expansionRate_pins :=\n  ⟨Checked.Cosmography.hubble, Checked.Fidelity.hubble_meets_spec, Real.exp, 0, Real.exp_pos 0,\n    Real.differentiableAt_exp, by rw [Real.deriv_exp]; exact (Real.exp_pos 0).le, trivial⟩\n\nend Checked.Trust.NV\n'
wr('Checked/Fidelity/ExpansionRatePin.lean',LEAN)
app('Checked.lean','import Checked.Fidelity.ExpansionRatePin')
app('scripts/trust/def_kinds.txt','Checked.Cosmography.expansionRate PHYSICS')
app('scripts/trust/pins.txt','Checked.Cosmography.expansionRate Checked.Cosmography.expansionRate_pins')
app('scripts/trust/phrases.txt','Checked.Cosmography.expansionRate | the Hubble rate a′(t)/a(t) of the scale factor {a} at time {t}')
app('scripts/trust/headlines.txt','Checked.Cosmography.expansionRate_timeReverse')
app('scripts/trust/headlines.txt','Checked.Cosmography.expansionRate_pins')
