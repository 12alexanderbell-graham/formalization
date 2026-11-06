"""Copy the Robertson t = 1e11 Work modules to Checked (namespace rename, specific Mathlib imports).
Pattern of runs/2026-11-06T0428Z/scripts/promote_rob.py. Work.Sim.{Robertson,RobCell,RobExists,OneSided}
already have Checked copies identical in code (docstrings differ only)."""
import re
TAC = ["Mathlib.Tactic.NormNum","Mathlib.Tactic.Linarith","Mathlib.Tactic.Ring","Mathlib.Tactic.FieldSimp","Mathlib.Tactic.Positivity","Mathlib.Tactic.Bound"]
base = ["Mathlib.Algebra.Order.Star.Real","Mathlib.Algebra.Order.Ring.Star","Mathlib.Analysis.Calculus.Deriv.Pow","Mathlib.Analysis.InnerProductSpace.Basic","Mathlib.Analysis.LocallyConvex.AbsConvexOpen","Mathlib.Analysis.SpecialFunctions.ExpDeriv","Mathlib.Topology.Algebra.Module.ModuleTopology"]
files = {
 'OneSidedNeg': base + ["Mathlib.Analysis.Calculus.MeanValue"],
 'ChebBound': base + ["Mathlib.RingTheory.Polynomial.Chebyshev","Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema"],
 'RobShear': base + ["Mathlib.Analysis.Calculus.MeanValue"],
 'RobLChain': [],
 'RobExistsLong': ["Mathlib.Algebra.Order.Star.Real","Mathlib.Analysis.LocallyConvex.AbsConvexOpen","Mathlib.Analysis.ODE.ExistUnique"],
 'RobLong': ["Mathlib.Analysis.Calculus.MeanValue","Mathlib.Analysis.Calculus.FDeriv.Prod"],
}
for i in range(8): files[f'RobLCerts{i}'] = []
for name, imps in files.items():
    src, dst = f'Work/Sim/{name}.lean', f'Checked/Sim/{name}.lean'
    orig = open(src).read()
    s = orig.replace('Work.Sim.', 'Checked.Sim.')
    out = []
    for l in s.split('\n'):
        out += [f'import {m}' for m in imps + TAC] if l.strip() == 'import Mathlib' else [l]
    s = '\n'.join(out)
    assert 'Work.' not in s, name
    open(dst, 'w').write(s)
    print(dst)
