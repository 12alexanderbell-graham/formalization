"""Promote the Gelfand multiplicity route from Work to Checked by script (run 2026-11-15T1828Z; after run
1228Z's promote_gelfand_extrema.py). Copies Work/Math/{GelfandPDEManyMain,GelfandPDEManyCentre}.lean to
Checked/Math/, renames the Work namespaces, drops `import Mathlib` from the headline module (the Main module
imports Checked modules only), replaces each module doc by one without numerals (check_prose rule 7)."""
import re
mods = ['GelfandPDEManyMain', 'GelfandPDEManyCentre']
docs = {
 'GelfandPDEManyMain': 'Gelfand problem in the three-dimensional ball as a PDE, `GelfandPDEManyMain`: the proof route of `Checked.Math.GelfandPDEManyCentre.gelfand_pde_radial_many_centre`. The construction of a radial solution from a radius s of the global regular solution W with s² e^{W(s)} = λ (from the proof of `Checked.Math.GelfandPDEExists.gelfand_pde_radial_exists`, for every radius), its value log(s²/λ) at the centre, and the intermediate value theorem on the segments between consecutive turning points of `Checked.Math.GelfandExtrema.gelfand_extrema`. No new certificates. Promoted from `Work/Math/GelfandPDEManyMain.lean`.',
 'GelfandPDEManyCentre': 'Gelfand problem in the three-dimensional ball as a PDE, `GelfandPDEManyCentre`: multiplicity of radial classical solutions, told apart by their values at the centre of the ball — a sequence of them at the parameter of the singular solution, as many as wanted for every parameter close enough to it, and two from that parameter up to the lower end of the window of the critical parameter of `Checked.Math.GelfandPDE.gelfand_pde_radial_bound`. Promoted from `Work/Math/GelfandPDEManyCentre.lean` (frozen, proved and audited by run 2026-11-15T1828Z; an earlier freeze that compared the solutions outside the ball fell to the referee); the route is `GelfandPDEManyMain`.',
}
for m in mods:
    s = open('Work/Math/%s.lean' % m).read()
    for n in mods:
        s = s.replace('Work.Math.%s' % n, 'Checked.Math.%s' % n)
    s = s.replace('import Mathlib\n', '', 1)
    s, k = re.subn(r'/-!.*?-/', lambda _: '/-! ' + docs[m] + ' -/', s, count=1, flags=re.S)
    assert k == 1
    s = re.sub(r'\n#print axioms[^\n]*\n?', '\n', s)
    s = s.rstrip('\n') + '\n'
    assert 'Work.' not in s, m
    open('Checked/Math/%s.lean' % m, 'w').write(s)
print('ok')
