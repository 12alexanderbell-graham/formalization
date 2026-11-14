"""Promote the second-minimum Bonnor–Ebert route from Work to Checked by script (run 2026-11-14T1428Z;
after run 1028Z's promote_be2.py). Copies Work/Math/{BEOCell,BEOData,BEOChain,BEOTail,BEOMain,BonnorEbertMin2}.lean
to Checked/Math/, renames the Work namespaces of these modules, and replaces each module doc by one without
numerals (check_prose rule 7)."""
import re
mods = ['BEOCell', 'BEOData', 'BEOChain', 'BEOTail', 'BEOMain', 'BonnorEbertMin2']
docs = {
 'BEOCell': 'Bonnor–Ebert sphere, `BEOCell`: one-sided (logarithmic-norm) validated cells for the isothermal equation in the homology variables. The cells of `BEHCell` bound the growth of the error with a Lipschitz constant, so their enclosure grows like a power of the radius although the true error contracts (the homology field spirals into its focus). Here the error is measured in a weighted norm taken from the real Jordan basis of the linearised field at the focus, in which the field has a negative one-sided bound on each cell; that bound is certified at the four corners of a box holding the cell polynomials and every point of the error ball (the field is quadratic, so its difference quotient is the Jacobian at the midpoint, which is affine in the midpoint). The enclosure then contracts instead of growing. Generic step `os_cell` (time-dependent field), cell check `CellProp` decided by the kernel, chains `chainTo`. Promoted from `Work/Math/BEOCell.lean`.',
 'BEOData': 'Bonnor–Ebert sphere, `BEOData`: the one-sided cells of `BEOCell` for the regular isothermal solution in homology variables from the end radius of `BEHChain` to the start of the tail, as data (generator `runs/2026-11-14T1428Z/scripts/gen_bo.py`, emitter `emit_bo.py`), each segment decided by kernel evaluation. Promoted from `Work/Math/BEOData.lean`.',
 'BEOChain': 'Bonnor–Ebert sphere, `BEOChain`: the one-sided cells of `BEOData` chained along every solution of the homology system that starts in the first cell\'s input box: the sign of 2u − v up to the bracket of the second maximum of the mass, the sign of its derivative and a box on that bracket, the sign of 2u − v up to the bracket of the second minimum, the sign of its derivative and a window of u on that bracket, the sign of 2u − v after it, and the state at the end radius. Promoted from `Work/Math/BEOChain.lean`.',
 'BEOTail': 'Bonnor–Ebert sphere, `BEOTail`: the lower bound of u v³ on the sublevel set of Volterra\'s function through the certified state at the end radius of the one-sided cells of `BEOData`, by the tangent-line inequality for the logarithm with negative slopes (convex duality from below, as in `BEHTail`). Promoted from `Work/Math/BEOTail.lean`.',
 'BEOMain': 'Bonnor–Ebert sphere, `BEOMain`: the assembly of `BEH2Main` (the first three extrema of the mass) continued by the one-sided cells of `BEOChain`: the zero of 2u − v in the bracket of the second minimum, the monotonicity of u v³ on either side of it from the second-maximum bracket on, and Volterra\'s function beyond the cells (`BEOTail`, bound from below). Promoted from `Work/Math/BEOMain.lean`.',
 'BonnorEbertMin2': 'Bonnor–Ebert sphere, `BonnorEbertMin2`: beyond the second maximum the pressure-confined mass falls to a second minimum, and that minimum is the strict minimum of the mass over every radius from the second maximum to the end of the solution. Promoted from `Work/Math/BonnorEbertMin2.lean` (frozen and proved by run 2026-11-14T1428Z); the route is `BEOMain` (one-sided cells in homology variables, then Volterra\'s function).',
}
for m in mods:
    s = open('Work/Math/%s.lean' % m).read()
    for n in mods:
        s = s.replace('Work.Math.%s' % n, 'Checked.Math.%s' % n)
    s = re.sub(r'/-!.*?-/', lambda _: '/-! ' + docs[m] + ' -/', s, count=1, flags=re.S)
    assert 'Work.' not in s, m
    open('Checked/Math/%s.lean' % m, 'w').write(s)
print('ok')
