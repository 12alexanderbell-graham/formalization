#!/usr/bin/env python3
"""Run 2026-11-12T1828Z: promote the reversed-flow Falkner–Skan rows β = −0.17, −0.18, −0.19 (β read blind from Ganapol 2010
Table 6 in run 2026-11-12T1428Z, readings fsAttThirdRhs / fsAttSecondRhs / fsAttLastRhs; the same rows head Ganapol's
reverse-flow Table 7) from Work/FalknerSkan/ReversedRows.lean to Checked/FalknerSkan/NegReversedRows.lean: statements
verbatim (names changed only), proofs as in Work, docstrings in the words of the promoted β = −0.1988 pair
(Checked/FalknerSkan/NegReversedWallShear.lean). Registers headlines and literal readings. Idempotent guards."""
import re, pathlib
R = pathlib.Path(__file__).resolve().parents[3]
ROWS = [('Seventeen', 'seventeen', '17', 'fsAttThirdRhs'), ('Eighteen', 'eighteen', '18', 'fsAttSecondRhs'),
        ('Nineteen', 'nineteen', '19', 'fsAttLastRhs')]
w = (R / 'Work/FalknerSkan/ReversedRows.lean').read_text()
body = ''
for Nm, nm, tag, rd in ROWS:
    a = w.index(f'theorem {nm}_sqrtK_pos')
    b = w.index(f'theorem fs_rev_{nm}_two_decay')
    b = w.index('\n\n', w.index('intro h; rw [h] at w2; linarith', b)) + 2
    t = w[a:b]
    # docstrings in the words of the promoted 1988 pair
    m = re.search(r'/-- Falkner–Skan with β = −(\d+)/100: there is a solution.*?-/', t, re.S); assert m
    lo, hi = re.search(r'(-0\.\d{10}) < q 0 ∧ q 0 < (-0\.\d{10}) :=', t).groups()
    t = t.replace(m.group(0), f"""/-- Falkner–Skan with β = −{tag}/100: there is a solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0 on [0, ∞) with
f(0) = 0, p(0) = 0, p → 1, −1 ≤ p ≤ 1 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`, with
−{lo[1:]} < q(0) < −{hi[1:]}. -/""")
    m = re.search(r'/-- Falkner–Skan with β = −(\d+)/100: there are solutions.*?-/', t, re.S); assert m
    t = t.replace(m.group(0), f"""/-- Falkner–Skan with β = −{tag}/100: there are solutions (f, p, q) and (f₂, p₂, q₂) of
f''' + f f'' + β(1 − f'²) = 0 on [0, ∞), both with f(0) = 0, p(0) = 0, p → 1 and −1 ≤ p ≤ 1 on [0, ∞), with
q(0) ≠ q₂(0), such that, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`, and,
for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p₂ η) ≤ q₂ η`. -/""")
    t = t.replace(f'fs_rev_{nm}_exists', f'fs_neg_reversed_wall_shear_{tag}_exists')
    t = t.replace(f'fs_rev_{nm}_two_decay', f'fs_neg_wall_shear_{tag}_two_decay')
    assert 'Work.' not in t and 'sorry' not in t, Nm
    body += t
head = (R / 'Checked/FalknerSkan/NegReversedWallShear.lean').read_text()
imports = head[:head.index('import Checked.')]
mods = [f'Checked.FSRev.R{Nm}{k}' for Nm, *_ in ROWS for k in ('Over', 'Slow', 'Tube')]
out = imports + 'import Checked.FSRev.RAssemble\nimport Checked.FalknerSkan.NegWallShearRows\n' + ''.join(f'import {m}\n' for m in mods) + """
/-! Falkner–Skan with adverse pressure gradient at the last three rows of an attached wall-shear table read blind, reversed-flow branch: a solution with negative wall shear that approaches the edge value faster than every exponential, and two solutions with different wall shear in that class. Module `NegReversedRows`, promoted from `Work/FalknerSkan/ReversedRows.lean`. -/

namespace Checked.FalknerSkan.NegReversedRows

open Set Filter Topology

""" + body + "end Checked.FalknerSkan.NegReversedRows\n"
(R / 'Checked/FalknerSkan/NegReversedRows.lean').write_text(out)
c = (R / 'Checked.lean').read_text()
if 'import Checked.FalknerSkan.NegReversedRows\n' not in c:
    c = c.replace('import Checked.FalknerSkan.NegWallShearRows\n', 'import Checked.FalknerSkan.NegWallShearRows\nimport Checked.FalknerSkan.NegReversedRows\n', 1)
    assert 'NegReversedRows' in c
(R / 'Checked.lean').write_text(c)
h = (R / 'scripts/trust/headlines.txt').read_text()
if 'fs_neg_reversed_wall_shear_17_exists' not in h:
    h += "# Falkner–Skan reversed-flow rows β = −0.17, −0.18, −0.19 (run 2026-11-12T1828Z; frozen 33cd0de, proved cab49ad on the reversed-flow stack generic in K, Checked/FSRev/; statements of the audited β = −1988/10000 reversed pair with β and window replaced; referee STANDS; β read blind in run 2026-11-12T1428Z)\n"
    for Nm, nm, tag, rd in ROWS:
        h += f"Checked.FalknerSkan.NegReversedRows.fs_neg_reversed_wall_shear_{tag}_exists\nChecked.FalknerSkan.NegReversedRows.fs_neg_wall_shear_{tag}_two_decay\n"
    (R / 'scripts/trust/headlines.txt').write_text(h)
L = (R / 'scripts/trust/literal_readings.txt').read_text()
S = 'Checked.Trust.SecondReading'
if 'fs_neg_reversed_wall_shear_17_exists' not in L:
    if not L.endswith('\n'): L += '\n'
    for Nm, nm, tag, rd in ROWS:
        tail = f'{S}.{rd} {S}.fskHalfLineTyped {S}.fskHalfLine {S}.fskWall {S}.fskEdge {S}.fsnDefectBelow {S}.stagSpeedBounded {S}.fsnWallValue'
        L += f'Checked.FalknerSkan.NegReversedRows.fs_neg_reversed_wall_shear_{tag}_exists {tail}\n'
        L += f'Checked.FalknerSkan.NegReversedRows.fs_neg_wall_shear_{tag}_two_decay {tail}\n'
    (R / 'scripts/trust/literal_readings.txt').write_text(L)
print('promoted')
