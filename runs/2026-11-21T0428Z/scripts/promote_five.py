"""Promote the contracting-cell route and the headline gelfand_turning_values_five from Work to Checked by script
(run 2026-11-21T0428Z; after runs/2026-11-20T1028Z/scripts/promote_turning.py). Copies
Work/Math/{GContract,GSeg,GSegData,GelfandLam4,GelfandTurningValuesFive}.lean to Checked/Math/, renames the Work
namespaces, replaces `import Mathlib` by specific modules and each module doc by one without numerals."""
import re
mods = ['GContract', 'GSeg', 'GSegData', 'GelfandLam4', 'GelfandTurningValuesFive']
ML = ('import Mathlib.Analysis.ODE.Gronwall\nimport Mathlib.Analysis.Calculus.Deriv.Slope\n'
      'import Mathlib.Analysis.SpecialFunctions.ExpDeriv\nimport Mathlib.Analysis.SpecialFunctions.Log.Basic\n'
      'import Mathlib.Analysis.Complex.Exponential\nimport Mathlib.Tactic.NormNum\nimport Mathlib.Tactic.Linarith\n'
      'import Mathlib.Tactic.Ring\nimport Mathlib.Tactic.FieldSimp\nimport Mathlib.Tactic.Positivity\n')
docs = {
 'GContract': 'Gelfand problem, `GContract`: contracting homology cells in log radius. In log radius the homology system is u′ = u (three − u − v), v′ = v (u − one); its right side is quadratic, so the difference of the field at two points is the Jacobian at their midpoint applied to their difference (`field_diff`). For the quadratic norm `Q` (the solution of the Lyapunov equation at the equilibrium) the form (P e) · J(m) e is affine in the midpoint m, so a bound by μ Q(e) on a box of midpoints follows from rational checks at its four corners (`box_bound`, `cornerOK`); with Grönwall\'s inequality this gives one cell (`ccell_q`) and a chain of cells decided as one Boolean (`chain_q`). Promoted from `Work/Math/GContract.lean` (run 2026-11-20T1628Z) by run 2026-11-21T0428Z.',
 'GSeg': 'Gelfand problem, `GSeg`: contracting homology cells with facts on the whole cell: the bound inside a cell (`ccell_in`), the link between cells (`link_q`), a chain with a property checked on every cell (`seg_all`, `seg_all\'`), the rational cell predicates for v below or above a level and u inside an interval (`vLtP`, `vGtP`, `uInP`), the change to log radius of the homology system (`log_radius`) and bounds on the exponential function from partial sums (`exp_ge_sum`, `exp_le_pow4`). Promoted from `Work/Math/GSeg.lean` (run 2026-11-21T0428Z).',
 'GSegData': 'Gelfand problem, `GSegData`: contracting homology cells in log radius from the end box of `GLamChain` through the fourth and fifth turning points, in six segments, as data (generator `runs/2026-11-21T0428Z/scripts/gen_seg.py`); each segment is decided by the kernel as one chain with its cell predicate, and consecutive segments are linked. Promoted from `Work/Math/GSegData.lean` (run 2026-11-21T0428Z).',
 'GelfandLam4': 'Gelfand problem, `GelfandLam4`: the value of the branch parameter λ(s) = s² e^{w(s)} of the regular isothermal solution at its fourth and fifth turning points, for every sequence of turning points with the monotonicity pattern of `Checked.Math.GelfandExtrema.gelfand_extrema`. Route: the route of `Checked.Math.GelfandLam3.lam3_band` up to the identification of the fourth turning point; then the contracting homology cells of `GSegData` in log radius from the end box of `GLamChain`: v above two before the first bracket, u in a window below one on it, v below two up to the second bracket, u in a window above one on it, v above two after it; the zeros of v − two in the brackets by the intermediate value theorem, the first equal to the fourth turning point (v strictly decreasing on the bracket of `GLam3Chain`), the second identified with the fifth turning point by strict monotonicity of λ at two points, and λ = two times u at a zero of v − two. Promoted from `Work/Math/GelfandLam4.lean` (run 2026-11-21T0428Z).',
 'GelfandTurningValuesFive': 'Gelfand problem in the three-dimensional ball, `GelfandTurningValuesFive`: the turning sequence of the radial solution branch of `Checked.Math.GelfandExtrema.gelfand_extrema`, with the value of the branch parameter enclosed at its first turning points (the five values of the conclusion). Promoted from `Work/Math/GelfandTurningValuesFive.lean` (frozen, proved and audited by run 2026-11-21T0428Z); the route is `Checked.Math.GelfandExtremaMain.main`, `Checked.Math.GLamBands.bands` and `Checked.Math.GelfandLam4.lam34_band`.',
}
for m in mods:
    s = open('Work/Math/%s.lean' % m).read()
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
