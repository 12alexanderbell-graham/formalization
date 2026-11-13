#!/usr/bin/env python3
"""Run 2026-11-13T0228Z: promote the reversed-flow Falkner–Skan row β = −0.03 of Ganapol 2010 Table 7
(Work/FalknerSkan/ReversedRowThree.lean, frozen 41e05bf / 5b588c7) into Checked/FalknerSkan/NegReversedWallShearRows.lean
(run 0028Z's module of the table rows): statement verbatim (name changed only), proof as in Work, docstring in the words
of the promoted rows. β read blind in this run (runs/2026-11-13T0228Z/fsrev_reader/, copied to
Checked/Trust/SecondReadingFSRevRowWanted.lean). Registers the headline and its literal reading. The module doc loses
its row count (disclosed in LEDGER). Template: runs/2026-11-13T0028Z/scripts/promote_rev_table.py. Idempotent guards."""
import re, pathlib, shutil
R = pathlib.Path(__file__).resolve().parents[3]
w = (R / 'Work/FalknerSkan/ReversedRowThree.lean').read_text()
a = w.index('theorem three_sqrtK_pos')
b = w.index('theorem fs_rev_three_exists')
b = w.index('linarith [three_hi_bound]', b)
b = w.index('\n', b) + 1
t = w[a:b] + '\n'
m = re.search(r'/-- Falkner–Skan with β = −(\d+)/100: there is a solution.*?-/', t, re.S); assert m and m.group(1) == '3'
lo, hi = re.search(r'(-0\.\d{10}) < q 0 ∧ q 0 < (-0\.\d{10}) :=', t).groups()
t = t.replace(m.group(0), f"""/-- Falkner–Skan with β = −3/100: there is a solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0 on [0, ∞) with
f(0) = 0, p(0) = 0, p → 1, −1 ≤ p ≤ 1 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`, with
−{lo[1:]} < q(0) < −{hi[1:]}. -/""")
t = t.replace('fs_rev_three_exists', 'fs_neg_reversed_wall_shear_3_exists')
assert 'Work.' not in t and 'sorry' not in t
P = R / 'Checked/FalknerSkan/NegReversedWallShearRows.lean'
c = P.read_text()
if 'fs_neg_reversed_wall_shear_3_exists' not in c:
    imp = 'import Checked.FSRev.RFourOver\n'
    assert imp in c
    c = c.replace(imp, 'import Checked.FSRev.RThreeOver\nimport Checked.FSRev.RThreeSlow\nimport Checked.FSRev.RThreeTube\n' + imp, 1)
    old = '/-! Falkner–Skan with adverse pressure gradient at twelve rows of a reversed-flow wall-shear table read blind:'
    assert old in c
    c = c.replace(old, '/-! Falkner–Skan with adverse pressure gradient at rows of a reversed-flow wall-shear table read blind:', 1)
    anchor = 'theorem four_sqrtK_pos'
    assert c.count(anchor) == 1
    c = c.replace(anchor, t + anchor, 1)
    P.write_text(c)
src = R / 'runs/2026-11-13T0228Z/fsrev_reader/SecondReadingFSRevTable.lean'
dst = R / 'Checked/Trust/SecondReadingFSRevRowWanted.lean'
shutil.copyfile(src, dst)
k = (R / 'Checked.lean').read_text()
imp, after = 'import Checked.Trust.SecondReadingFSRevRowWanted\n', 'import Checked.Trust.SecondReadingFSRevTableRows\n'
if imp not in k:
    assert after in k
    k = k.replace(after, after + imp, 1)
(R / 'Checked.lean').write_text(k)
H = 'Checked.FalknerSkan.NegReversedWallShearRows.fs_neg_reversed_wall_shear_3_exists'
h = (R / 'scripts/trust/headlines.txt').read_text()
if H not in h:
    if not h.endswith('\n'): h += '\n'
    h += ("# Falkner–Skan reversed-flow row β = −0.03 of Ganapol 2010 Table 7 (run 2026-11-13T0228Z; frozen 41e05bf, proved on "
          "the reversed-flow stack generic in K, Checked/FSRev/RThree*; statement of the audited β = −1988/10000 reversed "
          "statement with β and window replaced; referee STANDS; β read blind in run 2026-11-13T0228Z)\n" + H + '\n')
    (R / 'scripts/trust/headlines.txt').write_text(h)
L = (R / 'scripts/trust/literal_readings.txt').read_text()
S = 'Checked.Trust.SecondReading'
if H not in L:
    if not L.endswith('\n'): L += '\n'
    L += (f'{H} {S}.fsRevRowWantedRhs {S}.fskHalfLineTyped {S}.fskHalfLine {S}.fskWall {S}.fskEdge '
          f'{S}.fsnDefectBelow {S}.stagSpeedBounded {S}.fsnWallValue\n')
    (R / 'scripts/trust/literal_readings.txt').write_text(L)
print('promoted')
