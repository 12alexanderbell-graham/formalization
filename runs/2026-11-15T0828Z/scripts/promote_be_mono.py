"""Promote the monotone-segments Bonnor–Ebert route from Work to Checked by script (run 2026-11-15T0828Z; after
run 0228Z's promote_be_all.py). Copies Work/Math/{BEMonoExt,BEMonoMain,BonnorEbertMono}.lean to Checked/Math/
(the last as BonnorEbertMonotone.lean: V13, 'mono' is not a claim word), renames the Work namespaces, replaces
each module doc by one without numerals (check_prose rule 7), replaces `import Mathlib` of the headline module by
the import of its route, and writes the headline docstring."""
import re
mods = ['BEMonoExt', 'BEMonoMain', 'BonnorEbertMono']
docs = {
 'BEMonoExt': 'Bonnor–Ebert sphere, `BEMonoExt`: the assembly of `Checked.Math.BE3Ext.main_ext` repeated with the monotone segments of the mass up to the third maximum: strictly increasing up to the first maximum and strictly monotone between consecutive certified extrema (the sign of 2u − v from the certified chains between the brackets, a zero of 2u − v in each bracket identified with the extremum by strictness, the first maximum from `bonnor_ebert_critical`). No new certificates. Promoted from `Work/Math/BEMonoExt.lean`.',
 'BEMonoMain': 'Bonnor–Ebert sphere, `BEMonoMain`: the assembly of `Checked.Math.BEAllMain.main` repeated with the monotone segments of the mass: strictly increasing up to the first maximum and strictly monotone between consecutive extrema (certified part from `BEMonoExt`, tail segments from the analytic argument of `BEFocus` near the focus of the homology field). Promoted from `Work/Math/BEMonoMain.lean`.',
 'BonnorEbertMono': 'Bonnor–Ebert sphere, `BonnorEbertMonotone`: the claim of `Checked.Math.BonnorEbertExtrema.bonnor_ebert_extrema` for the same sequence of extrema, together with the strict monotonicity of the pressure-confined mass on the segment from the centre to the first maximum and on every segment between consecutive extrema, so that the sequence contains every local extremum of the mass. Promoted from `Work/Math/BonnorEbertMono.lean` (frozen, proved and audited by run 2026-11-15T0828Z); the route is `BEMonoMain`.',
}
headdoc = '''/-- Bonnor–Ebert sphere, extrema and monotone segments of the mass: for every solution w of
w'' + (2/s)w' + e^w = 0 on (0, ∞) with w(0) = 0, w differentiable on [0, ∞) with derivative φ and φ
continuous at 0, with m(s) = s² (−φ(s)) e^{w(s)/2} / √(4π), there is a strictly increasing sequence of radii
ξ(0) < ξ(1) < … tending to infinity, with ξ(0) between 6.4507514 and 6.4507515, such that m(s) < m(ξ(0)) for
s ≥ 0 with s ≠ ξ(0); for every k, m(ξ(2k+1)) < m(s) for s ≥ ξ(2k) with s ≠ ξ(2k+1), and m(s) < m(ξ(2k+2))
for s ≥ ξ(2k+1) with s ≠ ξ(2k+2); for every k, m(ξ(2k+1)) < √(2/π) < m(ξ(2k)); m(s) tends to √(2/π) as s
tends to infinity; m is strictly increasing on [0, ξ(0)]; and for every k, m is strictly decreasing on
[ξ(2k), ξ(2k+1)] and strictly increasing on [ξ(2k+1), ξ(2k+2)]. -/'''
for m in mods:
    s = open('Work/Math/%s.lean' % m).read()
    for n in mods:
        s = s.replace('Work.Math.%s' % n, 'Checked.Math.%s' % n)
    if m == 'BonnorEbertMono':
        s = s.replace('import Mathlib\n', '', 1)
    s = re.sub(r'/-!.*?-/', lambda _: '/-! ' + docs[m] + ' -/', s, count=1, flags=re.S)
    s = re.sub(r'\n#print axioms[^\n]*\n?', '\n', s)
    if m == 'BonnorEbertMono':
        s, k = re.subn(r'/-- Bonnor–Ebert sphere, extrema and monotone segments.*?-/', lambda _: headdoc, s, count=1, flags=re.S)
        assert k == 1
        s = s.replace('Checked.Math.BonnorEbertMono', 'Checked.Math.BonnorEbertMonotone')
    s = s.rstrip('\n') + '\n'
    assert 'Work.' not in s, m
    out = {'BonnorEbertMono': 'BonnorEbertMonotone'}.get(m, m)
    open('Checked/Math/%s.lean' % out, 'w').write(s)
print('ok')
