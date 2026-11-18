"""Promote the Bonnor–Ebert exact-count route from Work to Checked by script (run 2026-11-18T1628Z; after run
2026-11-18T0428Z's promote_gelfand_count.py). Copies Work/Math/{BonnorEbertCountMain,BonnorEbertCount}.lean to
Checked/Math/, renames the Work namespaces, replaces `import Mathlib` by the specific import found by
`#min_imports` (Mathlib.Order.CompletePartialOrder) in the route and by the route in the headline module,
replaces each module doc by one without numerals (check_prose rule 7)."""
import re
mods = ['BonnorEbertCountMain', 'BonnorEbertCount']
docs = {
 'BonnorEbertCountMain': 'Bonnor–Ebert sphere, `BonnorEbertCountMain`: the proof route of `Checked.Math.BonnorEbertCount.bonnor_ebert_count`. `count_abstract`: for a continuous function on the half-line vanishing at the centre with a strictly increasing sequence of strict alternating extrema (the facts of `Checked.Math.BonnorEbertMonotone.bonnor_ebert_extrema_monotone`), prepend the centre to the sequence (`shiftSeq`); in each segment where the value lies strictly between the end values there is exactly one root (`seg_root`: intermediate value theorem and injectivity), so the roots below the end of a segment are counted by induction (`count_prefix`, `count_total`) and the roots beyond it are read off the strict extremum properties; the maxima decrease, the minima increase, every maximum lies above the limit value and every minimum below. `ident_max`, `ident_min`: a strict extremum on a bounded interval, below its right end, equals the strict extremum from the same left end on, when the function is strictly monotone between them; this identifies the extremisers of the bounded-interval headlines (`bonnor_ebert_max`, `bonnor_ebert_min`, `bonnor_ebert_second_max`, `bonnor_ebert_second_min`, `bonnor_ebert_third_max`) with the first five terms of the sequence and gives their value windows. No new certificates. Promoted from `Work/Math/BonnorEbertCountMain.lean`.',
 'BonnorEbertCount': 'Bonnor–Ebert sphere, `BonnorEbertCount`: the exact number of radii at which the pressure-confined mass takes a given positive value (the number of equilibrium isothermal spheres of given mass, temperature and external pressure), for every value: none above the critical mass, one at it, and between consecutive extreme values a count that grows by one at every extreme value; infinitely many at the limit value of the mass; the first five extreme values enclosed. Promoted from `Work/Math/BonnorEbertCount.lean` (frozen, proved and audited by run 2026-11-18T1628Z); the route is `BonnorEbertCountMain`.',
}
for m in mods:
    s = open('Work/Math/%s.lean' % m).read()
    for n in mods:
        s = s.replace('Work.Math.%s' % n, 'Checked.Math.%s' % n)
    if m == 'BonnorEbertCount':
        s = s.replace('import Mathlib\n', '', 1)
        s = re.sub(r'import Checked\.Math\.BonnorEbert(Monotone|Max|Min|Max2|Min2|Max3)\n', '', s)
    else:
        s = s.replace('import Mathlib\n', 'import Mathlib.Order.CompletePartialOrder\n', 1)
    s, k = re.subn(r'/-!.*?-/', lambda _: '/-! ' + docs[m] + ' -/', s, count=1, flags=re.S)
    assert k == 1
    s = re.sub(r'\n#print axioms[^\n]*\n?', '\n', s)
    s = s.rstrip('\n') + '\n'
    assert 'Work.' not in s, m
    assert 'import Mathlib\n' not in s, m
    open('Checked/Math/%s.lean' % m, 'w').write(s)
print('ok')
