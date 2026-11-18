"""Promote the Gelfand count for every positive parameter from Work to Checked by script (run 2026-11-18T2228Z;
after run 2026-11-18T1628Z's promote_be_count.py). Copies Work/Math/{GelfandPDECountTurningMain,
GelfandPDECountTurning}.lean to Checked/Math/, renames the Work namespaces, drops `import Mathlib` (the route
imports only Checked modules; the headline module imports the route), replaces each module doc by one without
numerals (check_prose rule 7)."""
import re
mods = ['GelfandPDECountTurningMain', 'GelfandPDECountTurning']
docs = {
 'GelfandPDECountTurningMain': 'Gelfand problem in the three-dimensional ball as a PDE, `GelfandPDECountTurningMain`: the proof route of `Checked.Math.GelfandPDECountTurning.gelfand_pde_radial_count_turning`. `cset_encard`: for a positive parameter the counted set (functions on the closed ball agreeing there with a radial solution) is the image of the radii s ≥ 0 with s² e^{W(s)} equal to the parameter under s ↦ W(s‖x‖) + log(s²/λ), and this map is injective there (distinct radii give distinct centre values), so the two sets have the same `Set.encard` (`Checked.Math.GelfandPDECountMain.profile`, `Checked.Math.GelfandPDEManyMain.radial_global`, `Checked.Math.GelfandPDEManyMain.ne_of_centre`). `main`: `Checked.Math.BonnorEbertCountMain.count_abstract` applied to the branch parameter with the turning sequence of `Checked.Math.GelfandExtrema.gelfand_extrema` and the limit two; the windows of the first minimum and the second maximum from `Checked.Math.GLamBands.bands`; the maxima decrease and the minima increase by the strict extremum properties. No new certificates. Promoted from `Work/Math/GelfandPDECountTurningMain.lean`.',
 'GelfandPDECountTurning': 'Gelfand problem in the three-dimensional ball as a PDE, `GelfandPDECountTurning`: the number of radial classical solutions for every positive parameter, counted as functions on the closed ball: none above the largest parameter, one at it, and between consecutive turning values of the branch parameter a count that grows by one at every turning value; ⊤ at the value two, the limit of the branch parameter; the first three turning values enclosed. Promoted from `Work/Math/GelfandPDECountTurning.lean` (frozen, proved and audited by run 2026-11-18T2228Z); the route is `GelfandPDECountTurningMain`.',
}
for m in mods:
    s = open('Work/Math/%s.lean' % m).read()
    for n in mods:
        s = s.replace('Work.Math.%s' % n, 'Checked.Math.%s' % n)
    s = s.replace('import Mathlib\n', '', 1)
    s, k = re.subn(r'/-!.*?-/', lambda _: '/-! ' + docs[m] + ' -/', s, count=1, flags=re.S)
    assert k == 1
    s = s.rstrip('\n') + '\n'
    assert 'Work.' not in s, m
    assert 'import Mathlib\n' not in s, m
    open('Checked/Math/%s.lean' % m, 'w').write(s)
print('ok')
