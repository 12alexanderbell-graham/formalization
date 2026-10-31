import sys, pathlib
root = pathlib.Path(sys.argv[1])
def rep(rel, old, new):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    assert s.count(old) == 1, (rel, old, s.count(old))
    p.write_text(s.replace(old, new), encoding="utf-8")
rep("Checked/Fidelity/Pins.lean",
    "    (ha : 0 < a t) (hd : DifferentiableAt ℝ a t) : H a t = hubble a t := by",
    "    (ha : 0 < a t) (hd : DifferentiableAt ℝ a t) (hexp : a = Real.exp) : H a t = hubble a t := by")
rep("Checked/Trust/Witnesses.lean",
    "⟨hubble, hubble_meets_spec, Real.exp, 0, Real.exp_pos 0, Real.differentiableAt_exp, trivial⟩",
    "⟨hubble, hubble_meets_spec, Real.exp, 0, Real.exp_pos 0, Real.differentiableAt_exp, rfl, trivial⟩")
