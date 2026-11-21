"""Promote Work.Cosmography.B1A3Bound.third_coefficient_lower_bound to Checked by script (run 2026-11-21T1828Z),
with the scratch necessity module of this run and the blind literal reading."""
import re, sys
OUT = sys.argv[1] if len(sys.argv) > 1 else '.'
W = 'Work.Cosmography.B1A3Bound.third_coefficient_lower_bound'
C = 'Checked.Cosmography.B1A3Bound.third_coefficient_lower_bound'
# 1. headline
s = open('Work/Cosmography/B1A3Bound.lean').read()
doc = ('B1 at fit level, `B1A3Bound`: a lower bound on the third coefficient of every cubic log-polynomial that '
       'matches an exact flat ΛCDM distance modulus at three sources over the quasar range, whatever its second '
       'coefficient. Promoted from `Work/Cosmography/B1A3Bound.lean` (frozen, proved and audited by run '
       '2026-11-21T1628Z; promoted by run 2026-11-21T1828Z); the route is '
       '`Checked.Cosmography.B1A3Tools.a3_bound_gen` with the generated cell certificates of '
       '`Checked.Cosmography.B1A3Certs`.')
s, k = re.subn(r'/-!.*?-/', lambda _: '/-! ' + doc + ' -/', s, count=1, flags=re.S)
assert k == 1
s = s.replace('namespace Work.Cosmography.B1A3Bound', 'namespace Checked.Cosmography.B1A3Bound')
s = s.replace('end Work.Cosmography.B1A3Bound', 'end Checked.Cosmography.B1A3Bound')
assert 'Work.' not in s
open(OUT + '/Checked/Cosmography/B1A3Bound.lean', 'w').write(s)
# 2. necessity
n = open('runs/2026-11-21T1828Z/lean/NecessityBO.lean').read()
n = n.replace('import Work.Cosmography.B1A3Bound', 'import Checked.Cosmography.B1A3Bound')
n = n.replace(W, C)
n = re.sub(r'\bthird_([hr]\d+)\b', r'third_coefficient_lower_bound_\1', n)
n = n.replace('theorem third_nv', 'theorem third_coefficient_lower_bound_nv')
mdoc = '''/-!
# Hypothesis necessity, B1 third-coefficient bound (trust track T2b; run 2026-11-21T1828Z)

Hypotheses of `Checked.Cosmography.B1A3Bound.third_coefficient_lower_bound`, numbered as `necessity%` numbers them.

* **NEEDED from the parent's witnesses.** The time order of the three sources and the redshifts of the middle and
  farthest sources were shown NEEDED for `Checked.Cosmography.B1FitRL19.rl19_box_unmatched` by witnesses whose cubic
  lies in the box of that statement, so its third coefficient is below the bound here; each witness is reused as it is.
* **NEEDED in the Einstein–de Sitter model.** Without the distance-modulus condition at one source, a cubic with a
  small or negative third coefficient matches the other two (`resid_band` of `Checked.Trust.NCAR`); without the
  redshift of the nearest source, that source is placed at the middle one.
* **REDUNDANT.** Positivity and differentiability of the scale factor and the positive present Hubble rate, by the
  parent's lemmas; positivity of the cubic at the nearest or at the middle source, because a cubic of positive
  linear coefficient that is not positive there but positive at the next source has a large third coefficient
  (`bo_alg1`, `bo_alg3`).
* **Non-vacuity** from the witness `Checked.Trust.NCBN.rl19_box_unmatched_h16`.
-/'''
n, k = re.subn(r'/-!.*?-/', lambda _: mdoc, n, count=1, flags=re.S)
assert k == 1
assert 'Work.' not in n and 'Scratch' not in n
open(OUT + '/Checked/Trust/NecessityBO.lean', 'w').write(n)
# 3. literal reading
r = open('runs/2026-11-21T1828Z/lit_reader/SecondReadingB1A3.lean').read()
rdoc = ('/-! Blind literal reading of the model and data constants of the B1 third-coefficient bound: the flat ΛCDM '
        'expansion law, the redshifts of the three sources and the distance-modulus tolerance. Copied verbatim (code) '
        'from `runs/2026-11-21T1828Z/lit_reader/SecondReadingB1A3.lean`, written by a blind reader (Sonnet subagent) '
        'from the brief committed alone before it in that folder. Source: the claim\'s own description; nothing '
        'external consulted. -/')
r, k = re.subn(r'/-!.*?-/', lambda _: rdoc, r, count=1, flags=re.S)
assert k == 1
open(OUT + '/Checked/Trust/SecondReadingB1A3.lean', 'w').write(r)
print('ok')
