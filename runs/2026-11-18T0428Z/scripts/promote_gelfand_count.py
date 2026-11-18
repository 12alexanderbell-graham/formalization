"""Promote the Gelfand exact-count route from Work to Checked by script (run 2026-11-18T0428Z; after run
2026-11-15T1828Z's promote_gelfand_many.py). Copies Work/Math/{IsoUniq,GelfandPDECountMain,GelfandPDECount}.lean
to Checked/Math/, renames the Work namespaces, drops `import Mathlib` from the headline module and
IsoUniq's Work import, replaces each module doc by one without numerals (check_prose rule 7)."""
import re
mods = ['IsoUniq', 'GelfandPDECountMain', 'GelfandPDECount']
docs = {
 'IsoUniq': 'Isothermal sphere and radial Gelfand equation, `IsoUniq`: uniqueness of the regular solution of the singular initial-value problem w\'\' + (2/s) w\' + e^w = 0 with given centre value, in the class of `Checked.Math.BEGlobalExists.exists_global` (w differentiable on [0, T] with derivative φ, φ continuous at the centre, the equation for s > 0; no value of φ at the centre assumed). Near the centre, with D the largest gap of the two solutions on a short interval [0, h], u = s²(φ₁ − φ₂) has derivative −s²(e^{w₁} − e^{w₂}), which bounds the gap of φ by a multiple of D h and the gap of w by a multiple of D h², so D vanishes when h is small; away from the centre the field is Lipschitz and Mathlib\'s `ODE_solution_unique_of_mem_Icc_right` applies. Promoted from `Work/Math/IsoUniq.lean` (run 2026-11-18T0428Z).',
 'GelfandPDECountMain': 'Gelfand problem in the three-dimensional ball as a PDE, `GelfandPDECountMain`: the proof route of `Checked.Math.GelfandPDECount.gelfand_pde_radial_count`. Every radial classical solution with a positive parameter is W(s‖x‖) + log(s²/λ) on the closed ball for a radius s with s² e^{W(s)} = λ, W the regular isothermal solution (`profile`: the reduction of `Checked.Math.GelfandPDE.gelfand_pde_radial_bound`, the scaling of `Checked.Math.GelfandODEBound.ode_bound`, the uniqueness `Checked.Math.IsoUniq.uniq_Icc` below the radius and continuity at it); conversely every such radius gives one (`Checked.Math.GelfandPDEManyMain.radial_global`), and distinct radii give distinct centre values; the radii are counted with the turning points of `Checked.Math.GelfandExtrema.gelfand_extrema`. No new certificates. Promoted from `Work/Math/GelfandPDECountMain.lean`.',
 'GelfandPDECount': 'Gelfand problem in the three-dimensional ball as a PDE, `GelfandPDECount`: exact counts of radial classical solutions, solutions counted as the same when they agree on the closed ball — none above the maximum of the branch parameter, one at it, two between the second maximum and it, one between zero and the first minimum, two at the first minimum and three at the second maximum. Promoted from `Work/Math/GelfandPDECount.lean` (frozen, re-frozen with the sharpness clauses after the referee, proved and audited by run 2026-11-18T0428Z); the route is `GelfandPDECountMain`.',
}
for m in mods:
    s = open('Work/Math/%s.lean' % m).read()
    for n in mods:
        s = s.replace('Work.Math.%s' % n, 'Checked.Math.%s' % n)
    s = s.replace('import Mathlib\n', '', 1) if m == 'GelfandPDECount' else s
    s, k = re.subn(r'/-!.*?-/', lambda _: '/-! ' + docs[m] + ' -/', s, count=1, flags=re.S)
    assert k == 1
    s = re.sub(r'\n#print axioms[^\n]*\n?', '\n', s)
    s = s.rstrip('\n') + '\n'
    assert 'Work.' not in s, m
    assert 'import Mathlib\n' not in s, m
    open('Checked/Math/%s.lean' % m, 'w').write(s)
print('ok')
