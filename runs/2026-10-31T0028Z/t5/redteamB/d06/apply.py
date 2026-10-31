import sys, pathlib
root = pathlib.Path(sys.argv[1])
def rep(rel, old, new):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    assert s.count(old) == 1, (rel, old, s.count(old))
    p.write_text(s.replace(old, new), encoding="utf-8")
rep("Checked/Cosmography/LookbackThird.lean",
    "(ha : ContDiffAt ℝ 3 a t₀) (ha0 : a t₀ ≠ 0) (hH : deriv a t₀ ≠ 0) :\n",
    "(ha : ContDiffAt ℝ 3 a t₀) (ha0 : a t₀ ≠ 0) (hH : deriv a t₀ ≠ 0)\n    (hq : decel a t₀ = -1) :\n")
rep("Checked/Trust/Witnesses.lean",
    "nonvacuity% Checked.Cosmography.lookback_second_order_bigO :=\n  ⟨Real.exp, 0, dS_smooth _, dS_a0, by simp [Real.deriv_exp], trivial⟩",
    "nonvacuity% Checked.Cosmography.lookback_second_order_bigO :=\n  ⟨Real.exp, 0, dS_smooth _, dS_a0, by simp [Real.deriv_exp], dS_decel, trivial⟩")
