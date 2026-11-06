"""Copy the Robertson Work modules to Checked (namespace rename, specific imports). Used on branch
wip/rob-checked (8d72e6b); imports from #min_imports on Mathlib-only scratch copies plus tactics."""
TAC = ["Mathlib.Tactic.NormNum","Mathlib.Tactic.Linarith","Mathlib.Tactic.Ring","Mathlib.Tactic.FieldSimp","Mathlib.Tactic.Positivity","Mathlib.Tactic.Bound"]
base = ["Mathlib.Algebra.Order.Star.Real","Mathlib.Algebra.Order.Ring.Star","Mathlib.Analysis.Calculus.Deriv.Pow","Mathlib.Analysis.InnerProductSpace.Basic","Mathlib.Analysis.LocallyConvex.AbsConvexOpen","Mathlib.Analysis.SpecialFunctions.ExpDeriv","Mathlib.Topology.Algebra.Module.ModuleTopology"]
files = {
 'Work/Sim/OneSided.lean': ('Checked/Sim/OneSided.lean', base + ["Mathlib.Analysis.Calculus.MeanValue"]),
 'Work/Sim/RobCell.lean': ('Checked/Sim/RobCell.lean', base),
 'Work/Sim/RobExists.lean': ('Checked/Sim/RobExists.lean', ["Mathlib.Algebra.Order.Star.Real","Mathlib.Analysis.LocallyConvex.AbsConvexOpen","Mathlib.Analysis.ODE.ExistUnique"]),
 'Work/Fidelity/RobSpec.lean': ('Checked/Fidelity/RobSpec.lean', base + ["Mathlib.Analysis.Calculus.Deriv.Inv","Mathlib.Analysis.Calculus.MeanValue"]),
 'Work/Sim/Robertson.lean': ('Checked/Sim/Robertson.lean', ["Mathlib.Analysis.Calculus.MeanValue","Mathlib.Analysis.Calculus.FDeriv.Prod"]),
 'Work/Sim/RobPin.lean': ('Checked/Sim/RobPin.lean', []),
}
for i in range(5): files[f'Work/Sim/RobCerts{i}.lean'] = (f'Checked/Sim/RobCerts{i}.lean', [])
for src, (dst, imps) in files.items():
    orig = open(src).read()
    s = orig.replace('Work.Sim.', 'Checked.Sim.').replace('Work.Fidelity.RobSpec', 'Checked.Fidelity.RobSpec')
    out = []
    for l in s.split('\n'):
        out += [f'import {m}' for m in imps + TAC] if l.strip() == 'import Mathlib' else [l]
    s = '\n'.join(out)
    if imps and 'import Mathlib\n' not in orig:
        s = '\n'.join(f'import {m}' for m in imps) + '\n' + s
    s = s.replace('inlined here by value: Work does not', 'inlined here by value: Checked does not')
    open(dst, 'w').write(s)
