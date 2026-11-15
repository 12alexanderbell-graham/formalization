"""Promote the Gelfand turning-point route from Work to Checked by script (run 2026-11-15T1228Z; after
run 0828Z's promote_be_mono.py). Copies Work/Math/{GelfandExtremaMain,GelfandExtrema}.lean to Checked/Math/,
renames the Work namespaces, replaces `import Mathlib` by specific imports, replaces each module doc by one
without numerals (check_prose rule 7)."""
import re, sys
mods = ['GelfandExtremaMain', 'GelfandExtrema']
extra = sys.argv[1:]  # extra Mathlib imports for the main module
docs = {
 'GelfandExtremaMain': 'Gelfand problem, `GelfandExtremaMain`: the proof route of `Checked.Math.GelfandExtrema.gelfand_extrema`, every turning point of the radial Gelfand branch in the three-dimensional ball. The turning points are the zeros of v − 2 in the homology variables u = s e^w / (−φ), v = −s φ (u v is the branch parameter); Volterra\'s function of (u, v) decreases along the solution and orders the extrema; the zeros of v − 2 are transversal and recur after every radius because the mass extrema of `Checked.Math.BonnorEbertExtrema.bonnor_ebert_extrema` recur; the first turning point and its value come from `Checked.Math.Gelfand.gelfand_ball_critical`. No new certificates. Promoted from `Work/Math/GelfandExtremaMain.lean`.',
 'GelfandExtrema': 'Gelfand problem in the three-dimensional ball, `GelfandExtrema`: every turning point of the radial solution branch at once — an infinite strictly increasing sequence of radii tending to infinity, alternating strict maxima and minima of the branch parameter, each the strict extreme from the previous one on, maxima above and minima below the value of the singular solution, to which the parameter tends, with strictly monotone segments in between; the first turning point in the window of `Checked.Math.Gelfand.gelfand_ball_critical`. Promoted from `Work/Math/GelfandExtrema.lean` (frozen, proved and audited by run 2026-11-15T1228Z); the route is `GelfandExtremaMain`.',
}
for m in mods:
    s = open('Work/Math/%s.lean' % m).read()
    for n in mods:
        s = s.replace('Work.Math.%s' % n, 'Checked.Math.%s' % n)
    if m == 'GelfandExtrema':
        s = s.replace('import Mathlib\n', '', 1)
    else:
        s = s.replace('import Mathlib\n', ''.join('import %s\n' % e for e in extra), 1)
    s, k = re.subn(r'/-!.*?-/', lambda _: '/-! ' + docs[m] + ' -/', s, count=1, flags=re.S)
    assert k == 1
    s = re.sub(r'\n#print axioms[^\n]*\n?', '\n', s)
    s = s.rstrip('\n') + '\n'
    assert 'Work.' not in s, m
    open('Checked/Math/%s.lean' % m, 'w').write(s)
print('ok')
