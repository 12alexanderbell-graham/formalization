"""Promote the every-extremum Bonnor–Ebert route from Work to Checked by script (run 2026-11-15T0228Z; after
run 1828Z's promote_be_max3.py). Copies Work/Math/{BEFocus,BEState300,BE3Ext,BEAllMain,BEGlobalExists,
BonnorEbertAll}.lean to Checked/Math/ (the last as BonnorEbertExtrema.lean), renames the Work namespaces of these modules, replaces each module doc by
one without numerals (check_prose rule 7), drops `#print axioms`, replaces all imports by the specific
imports of imports.json (found with `#min_imports` on the copies built with `import Mathlib`), and writes the headline docstring."""
import re, sys
mods = ['BEFocus', 'BEState300', 'BE3Ext', 'BEAllMain', 'BEGlobalExists', 'BonnorEbertAll']
IMPORTS = {m: ['Mathlib'] for m in mods}
try:
    import json
    IMPORTS.update(json.load(open('runs/2026-11-15T0228Z/scripts/imports.json')))
except FileNotFoundError:
    pass
docs = {
 'BEFocus': 'Bonnor–Ebert sphere, `BEFocus`: the homology system u\' = u(3 − u − v)/t, v\' = v(u − 1)/t near its focus, with no certificates. In the weighted norm `Checked.Math.BEOCell.Nw` of the focus\' real Jordan basis a small ball about the focus is forward invariant and `Nw` decreases along every solution in it; the angular momentum about the focus is positive, so 2u − v changes sign again after every radius, each zero transversal, and at the zeros `Nw` is a fixed multiple of (u − 1)². Promoted from `Work/Math/BEFocus.lean`.',
 'BEState300': 'Bonnor–Ebert sphere, `BEState300`: what the certified chains of `BE3Main` say at the end radius of the one-sided cells, exported for `BonnorEbertAll`: φ < 0 beyond the decrease range of the first maximum, the homology state (u, v) at the end radius in a small box about a rational point, and 2u − v < 0 from the third-maximum bracket to the end radius. Promoted from `Work/Math/BEState300.lean`.',
 'BE3Ext': 'Bonnor–Ebert sphere, `BE3Ext`: the assembly of `Checked.Math.BE3Main` repeated with two more outputs (the mass window at the second minimum, and u v³ strictly decreasing from the third maximum to the end radius of the cells), for `BonnorEbertAll`. Promoted from `Work/Math/BE3Ext.lean`.',
 'BEAllMain': 'Bonnor–Ebert sphere, `BEAllMain`: the assembly behind `Checked.Math.BonnorEbertAll.bonnor_ebert_all_extrema`: the first five extrema from the certified chain (`BE3Ext`), the state at the end radius of the cells (`BEState300`), and every later extremum from the analytic argument near the focus of the homology field (`BEFocus.tail`), joined through u v³ = 4π m². Promoted from `Work/Math/BEAllMain.lean`.',
 'BEGlobalExists': 'Bonnor–Ebert sphere, `BEGlobalExists`: the regular solution of the isothermal equation w\'\' + (2/s) w\' + e^w = 0, w(0) = 0, exists on the whole half-line (one-sided derivatives within it, φ = w\' continuous at the centre). Route: the left part of `Checked.Math.GExistsLeft.exists_left`, then the right parts of `Checked.Math.GExistsRight.exists_right` on longer and longer intervals, which agree on their common interval by uniqueness of the regular ODE (`ODE_solution_unique_of_mem_Icc_right`); the global right part takes at t the solution with index ⌈t⌉₊. Promoted from `Work/Math/BEGlobalExists.lean`.',
 'BonnorEbertAll': 'Bonnor–Ebert sphere, `BonnorEbertAll`: every extremum of the pressure-confined mass at once, for the regular isothermal solution on the whole half-line: an infinite strictly increasing sequence of extrema tending to infinity, alternating maxima and minima, each the strict extreme of the mass from the previous extremum on, maxima above and minima below the singular isothermal sphere\'s value, to which the mass tends. Promoted from `Work/Math/BonnorEbertAll.lean` (frozen and proved by run 2026-11-15T0028Z); the route is `BEAllMain` (the certified chain of `BE3Ext`, then the analytic argument of `BEFocus` near the focus of the homology field).',
}
headdoc = open('runs/2026-11-15T0228Z/scripts/headdoc.txt').read().rstrip('\n') if len(sys.argv) < 2 else None
for m in mods:
    s = open('Work/Math/%s.lean' % m).read()
    for n in mods:
        s = s.replace('Work.Math.%s' % n, 'Checked.Math.%s' % n)
    lines = s.split('\n')
    body_start = 0
    while lines[body_start].startswith('import '):
        body_start += 1
    imps = [l for l in lines[:body_start] if l != 'import Mathlib']
    new_imps = ['import %s' % i for i in IMPORTS[m]]
    s = '\n'.join(new_imps + lines[body_start:])
    s = re.sub(r'/-!.*?-/', lambda _: '/-! ' + docs[m] + ' -/', s, count=1, flags=re.S)
    s = re.sub(r'\n#print axioms[^\n]*\n?', '\n', s)
    if m == 'BonnorEbertAll' and headdoc:
        s, k = re.subn(r'/-- Bonnor–Ebert sphere, every extremum of the mass.*?-/', lambda _: headdoc, s, count=1, flags=re.S)
        assert k == 1
    s = s.rstrip('\n') + '\n'
    # Checked names (V8/V13 of check_claim_vocab.py: 'all' is a strength word and may not appear in a headline's
    # name, module component included): module BonnorEbertAll -> BonnorEbertExtrema, theorem
    # bonnor_ebert_all_extrema -> bonnor_ebert_extrema (statement unchanged; LEDGER).
    s = s.replace('Checked.Math.BonnorEbertAll', 'Checked.Math.BonnorEbertExtrema')
    s = s.replace('bonnor_ebert_all_extrema', 'bonnor_ebert_extrema')
    s = s.replace('`BonnorEbertAll`', '`BonnorEbertExtrema`')
    assert 'Work.' not in s, m
    out = {'BonnorEbertAll': 'BonnorEbertExtrema'}.get(m, m)
    open('Checked/Math/%s.lean' % out, 'w').write(s)
print('ok')
