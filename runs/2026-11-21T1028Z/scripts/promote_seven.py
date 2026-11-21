"""Promote GSegData7, GelfandLam6 and the headline gelfand_turning_values_seven from Work to Checked by script
(run 2026-11-21T1028Z; after runs/2026-11-21T0428Z/scripts/promote_five.py)."""
import re
mods = ['GSegData7', 'GelfandLam6', 'GelfandTurningValuesSeven']
ML = ('import Mathlib.Analysis.ODE.Gronwall\nimport Mathlib.Analysis.Calculus.Deriv.Slope\n'
      'import Mathlib.Analysis.SpecialFunctions.ExpDeriv\nimport Mathlib.Analysis.SpecialFunctions.Log.Basic\n'
      'import Mathlib.Analysis.Complex.Exponential\nimport Mathlib.Tactic.NormNum\nimport Mathlib.Tactic.Linarith\n'
      'import Mathlib.Tactic.Ring\nimport Mathlib.Tactic.FieldSimp\nimport Mathlib.Tactic.Positivity\n')
docs = {
 'GSegData7': 'Gelfand problem, `GSegData7`: contracting homology cells in log radius continuing the chain of `GSegData` from its last cell through the sixth and seventh turning points, in five segments, as data (generator `runs/2026-11-21T1028Z/scripts/gen_seg7.py`); each segment is decided by the kernel as one chain with its cell predicate, and consecutive segments are linked. Promoted from `Work/Math/GSegData7.lean` (run 2026-11-21T1028Z).',
 'GelfandLam6': 'Gelfand problem, `GelfandLam6`: the value of the branch parameter λ(s) = s² e^{w(s)} of the regular isothermal solution at its fourth to seventh turning points, for every sequence of turning points with the monotonicity pattern of `Checked.Math.GelfandExtrema.gelfand_extrema`. Route: the proof of `Checked.Math.GelfandLam4.lam34_band`, continued from the last cell of `GSegData` through the segments of `GSegData7` (v above two, u in a window below one, v below two, u in a window above one, v above two); the zeros of v − two in the two new brackets by the intermediate value theorem, identified with the sixth and seventh turning points by strict monotonicity of λ at two points, and λ = two times u at a zero of v − two. Promoted from `Work/Math/GelfandLam6.lean` (run 2026-11-21T1028Z).',
 'GelfandTurningValuesSeven': 'Gelfand problem in the three-dimensional ball, `GelfandTurningValuesSeven`: the turning sequence of the radial solution branch of `Checked.Math.GelfandExtrema.gelfand_extrema`, with the value of the branch parameter enclosed at its first turning points (the seven values of the conclusion). Promoted from `Work/Math/GelfandTurningValuesSeven.lean` (frozen, proved and audited by run 2026-11-21T1028Z); the route is `Checked.Math.GelfandExtremaMain.main`, `Checked.Math.GLamBands.bands` and `Checked.Math.GelfandLam6.lam3456_band`.',
}
for m in mods:
    s = open('Work/Math/%s.lean' % m).read()
    if s.startswith('import Mathlib\n'):
        s = s.replace('import Mathlib\n', ML, 1)
    for n in mods:
        s = s.replace('Work.Math.%s' % n, 'Checked.Math.%s' % n)
    s, k = re.subn(r'/-!.*?-/', lambda _: '/-! ' + docs[m] + ' -/', s, count=1, flags=re.S)
    assert k == 1
    s = s.rstrip('\n') + '\n'
    assert 'Work.' not in s, m
    assert 'import Mathlib\n' not in s, m
    open('Checked/Math/%s.lean' % m, 'w').write(s)
print('ok')
