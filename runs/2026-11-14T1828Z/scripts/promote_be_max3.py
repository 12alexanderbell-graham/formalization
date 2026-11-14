"""Promote the third-maximum Bonnor–Ebert route from Work to Checked by script (run 2026-11-14T1828Z; after
run 1428Z's promote_be_min2.py). Copies Work/Math/{BE3Data,BE3Chain,BE3Tail,BE3Main,BonnorEbertMax3}.lean to
Checked/Math/, renames the Work namespaces of these modules, replaces each module doc by one without numerals
(check_prose rule 7), drops `#print axioms`, and writes the headline docstring in the house style of
`Checked.Math.BonnorEbertMin2`."""
import re
mods = ['BE3Data', 'BE3Chain', 'BE3Tail', 'BE3Main', 'BonnorEbertMax3']
docs = {
 'BE3Data': 'Bonnor–Ebert sphere, `BE3Data`: the one-sided cells of `BEOCell` for the regular isothermal solution in homology variables from the end radius of `BEOChain` to the start of the tail, as data (generator `runs/2026-11-14T1828Z/scripts/gen_b3.py`, emitter `emit_b3.py`), each segment decided by kernel evaluation. Promoted from `Work/Math/BE3Data.lean`.',
 'BE3Chain': 'Bonnor–Ebert sphere, `BE3Chain`: the one-sided cells of `BE3Data` chained along every solution of the homology system that starts in the first cell\'s input box: the sign of 2u − v up to the bracket of the third maximum of the mass, the sign of its derivative and a window of u on that bracket, the sign of 2u − v after it, and the state at the end radius. Promoted from `Work/Math/BE3Chain.lean`.',
 'BE3Tail': 'Bonnor–Ebert sphere, `BE3Tail`: the upper bound of u v³ on the sublevel set of Volterra\'s function through the certified state at the end radius of the one-sided cells of `BE3Data`, by the tangent-line inequality for the logarithm with positive slopes (convex duality from above, as in `BEH2Tail`). Promoted from `Work/Math/BE3Tail.lean`.',
 'BE3Main': 'Bonnor–Ebert sphere, `BE3Main`: the assembly of `BEOMain` (the first four extrema of the mass) continued by the one-sided cells of `BE3Chain`: the zero of 2u − v in the bracket of the second minimum identified with the second minimiser by uniqueness, the zero of 2u − v in the bracket of the third maximum, the monotonicity of u v³ on either side of it from the second minimum on, and Volterra\'s function beyond the cells (`BE3Tail`, bound from above). Promoted from `Work/Math/BE3Main.lean`.',
 'BonnorEbertMax3': 'Bonnor–Ebert sphere, `BonnorEbertMax3`: beyond the second minimum the pressure-confined mass rises to a third maximum, and that maximum is the strict maximum of the mass over every radius from the second minimum to the end of the solution. Promoted from `Work/Math/BonnorEbertMax3.lean` (frozen and proved by run 2026-11-14T1828Z); the route is `BE3Main` (one-sided cells in homology variables, then Volterra\'s function).',
}
headdoc = '''/-- Bonnor–Ebert sphere, third max of the mass: for every S ≥ 300000 and every solution w of
w'' + (2/s)w' + e^w = 0 on (0, S] with w(0) = 0, w differentiable on [0, S] with derivative φ and φ continuous
at 0, with m(s) = s² (−φ(s)) e^{w(s)/2} / √(4π), there are ξ₁ between 6.4507514 and 6.4507515, ξ₂
between 67.0075 and 67.0076, ξ₃ between 733.5 and 734, ξ₄ between 7849.5 and 7849.75 and ξ₅ between 84497
and 84516 such that m(s) < m(ξ₁) for s in [0, S] with s ≠ ξ₁, m(ξ₂) < m(s) for s in [ξ₁, S] with s ≠ ξ₂,
m(s) < m(ξ₃) for s in [ξ₂, S] with s ≠ ξ₃, m(ξ₄) < m(s) for s in [ξ₃, S] with s ≠ ξ₄, m(s) < m(ξ₅) for s
in [ξ₄, S] with s ≠ ξ₅, m(ξ₅) lies between 0.80091 and 0.800916, and the density contrast e^{−w(ξ₅)} lies
between 3556300000 and 3558000000. -/'''
for m in mods:
    s = open('Work/Math/%s.lean' % m).read()
    for n in mods:
        s = s.replace('Work.Math.%s' % n, 'Checked.Math.%s' % n)
    s = re.sub(r'/-!.*?-/', lambda _: '/-! ' + docs[m] + ' -/', s, count=1, flags=re.S)
    s = re.sub(r'\n#print axioms[^\n]*\n?', '\n', s)
    if m == 'BonnorEbertMax3':
        s = re.sub(r'/-- Bonnor–Ebert sphere, the third maximum.*?-/', lambda _: headdoc, s, count=1, flags=re.S)
        assert 'third max of the mass' in s
    s = s.rstrip('\n') + '\n'
    assert 'Work.' not in s, m
    open('Checked/Math/%s.lean' % m, 'w').write(s)
print('ok')
