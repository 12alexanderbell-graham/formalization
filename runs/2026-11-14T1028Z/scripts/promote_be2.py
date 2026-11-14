"""Promote the second-maximum Bonnor–Ebert route from Work to Checked by script (run 2026-11-14T1028Z).
Copies Work/Math/{BEH2Data,BEH2Chain,BEH2Tail,BEH2Main,BonnorEbertMax2}.lean to Checked/Math/, renames the
Work namespaces of these modules, and replaces each module doc by one without numerals (check_prose rule 7)."""
import re
mods = ['BEH2Data', 'BEH2Chain', 'BEH2Tail', 'BEH2Main', 'BonnorEbertMax2']
docs = {
 'BEH2Data': 'Bonnor–Ebert sphere, `BEH2Data`: the validated cells of the regular isothermal solution in homology variables from the end radius of `BEHChain` to the start of the tail, as data (generator `runs/2026-11-14T1028Z/scripts/gen_bh2.py`, emitter `emit_bh2.py`), each segment decided by kernel evaluation: 2u − v positive up to the bracket cell of the second maximum of the mass, the bracket cell, and 2u − v negative after it. Promoted from `Work/Math/BEH2Data.lean`.',
 'BEH2Chain': 'Bonnor–Ebert sphere, `BEH2Chain`: the cells of `BEH2Data` chained along every solution of the homology system that starts in the first cell\'s input box: the sign of 2u − v before and after the bracket cell of the second maximum of the mass, the sign of its derivative and a window of u on the bracket cell, and the state at the end radius. Promoted from `Work/Math/BEH2Chain.lean`.',
 'BEH2Tail': 'Bonnor–Ebert sphere, `BEH2Tail`: the upper bound of u v³ on the sublevel set of Volterra\'s function through the certified state at the end radius of the cells of `BEH2Data`, by the tangent-line inequality for the logarithm with positive slopes (convex duality from above). Promoted from `Work/Math/BEH2Tail.lean`.',
 'BEH2Main': 'Bonnor–Ebert sphere, `BEH2Main`: the assembly of `BEHMain` (certified cells and the first minimum of the mass) continued by the certified cells of `BEH2Chain`: the zero of 2u − v in the second bracket cell (the second maximum of the mass), the monotonicity of u v³ on either side of it, and Volterra\'s function beyond the cells (`BEH2Tail`, bound from above). Promoted from `Work/Math/BEH2Main.lean`.',
 'BonnorEbertMax2': 'Bonnor–Ebert sphere, `BonnorEbertMax2`: beyond the first minimum the pressure-confined mass rises to a second maximum, and that maximum is the strict maximum of the mass over every radius from the first minimum to the end of the solution. Promoted from `Work/Math/BonnorEbertMax2.lean` (frozen and proved by run 2026-11-14T1028Z); the route is `BEH2Main` (certified cells in homology variables, then Volterra\'s function).',
}
for m in mods:
    s = open('Work/Math/%s.lean' % m).read()
    for n in mods:
        s = s.replace('Work.Math.%s' % n, 'Checked.Math.%s' % n)
    s = re.sub(r'/-!.*?-/', lambda _: '/-! ' + docs[m] + ' -/', s, count=1, flags=re.S)
    assert 'Work.' not in s, m
    open('Checked/Math/%s.lean' % m, 'w').write(s)
print('ok')
