#!/usr/bin/env python3
"""Run 2026-11-13T0028Z: promote twelve reversed-flow Falkner–Skan rows of Ganapol 2010 Table 7 — β = −0.04 … −0.09,
−0.11 … −0.14 (Work/FalknerSkan/ReversedTable.lean, frozen cf66704, run 2026-11-12T2228Z), −0.15
(Work/FalknerSkan/ReversedRows.lean, frozen 33cd0de, run 2026-11-12T1828Z) and −0.16 (ReversedTable) — to
Checked/FalknerSkan/NegReversedWallShearRows.lean: statements verbatim (names changed only), proofs as in Work, docstrings
in the words of the promoted rows (Checked/FalknerSkan/NegReversedRows.lean). β read blind from Table 7 in this run
(runs/2026-11-13T0028Z/fsrev_reader/, copied to Checked/Trust/SecondReadingFSRevTable.lean). Registers headlines
and literal readings. Idempotent guards. Template: runs/2026-11-12T1828Z/scripts/promote_rev_rows.py."""
import re, pathlib
R = pathlib.Path(__file__).resolve().parents[3]
ROWS = [('Four', 'four', '4', 'T'), ('Five', 'five', '5', 'T'), ('Six', 'six', '6', 'T'), ('Seven', 'seven', '7', 'T'),
        ('Eight', 'eight', '8', 'T'), ('Nine', 'nine', '9', 'T'), ('Eleven', 'eleven', '11', 'T'),
        ('Twelve', 'twelve', '12', 'T'), ('Thirteen', 'thirteen', '13', 'T'), ('Fourteen', 'fourteen', '14', 'T'),
        ('Fifteen', 'fifteen', '15', 'R'), ('Sixteen', 'sixteen', '16', 'T')]
SRC = {'T': (R / 'Work/FalknerSkan/ReversedTable.lean').read_text(),
       'R': (R / 'Work/FalknerSkan/ReversedRows.lean').read_text()}
body = ''
for Nm, nm, tag, src in ROWS:
    w = SRC[src]
    a = w.index(f'theorem {nm}_sqrtK_pos')
    b = w.index(f'theorem fs_rev_{nm}_exists')
    b = w.index(f'linarith [{nm}_hi_bound]', b)
    b = w.index('\n', b) + 1
    t = w[a:b] + '\n'
    m = re.search(r'/-- Falkner–Skan with β = −(\d+)/100: there is a solution.*?-/', t, re.S); assert m, Nm
    assert m.group(1) == tag, (Nm, m.group(1))
    lo, hi = re.search(r'(-0\.\d{10}) < q 0 ∧ q 0 < (-0\.\d{10}) :=', t).groups()
    t = t.replace(m.group(0), f"""/-- Falkner–Skan with β = −{tag}/100: there is a solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0 on [0, ∞) with
f(0) = 0, p(0) = 0, p → 1, −1 ≤ p ≤ 1 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`, with
−{lo[1:]} < q(0) < −{hi[1:]}. -/""")
    t = t.replace(f'fs_rev_{nm}_exists', f'fs_neg_reversed_wall_shear_{tag}_exists')
    assert 'Work.' not in t and 'sorry' not in t, Nm
    body += t
head = (R / 'Checked/FalknerSkan/NegReversedRows.lean').read_text()
imports = head[:head.index('import Checked.')]
mods = ['Checked.FSRev.RAssemble', 'Checked.FSRev.RAssembleA'] + \
    [f'Checked.FSRev.R{Nm}{k}' for Nm, *_ in ROWS for k in ('Over', 'Slow', 'Tube')]
out = imports + ''.join(f'import {m}\n' for m in mods) + """
/-! Falkner–Skan with adverse pressure gradient at twelve rows of a reversed-flow wall-shear table read blind: for each row, a solution with negative wall shear that approaches the edge value faster than every exponential. Module `NegReversedWallShearRows`, promoted from `Work/FalknerSkan/ReversedTable.lean` and `Work/FalknerSkan/ReversedRows.lean`. -/

namespace Checked.FalknerSkan.NegReversedWallShearRows

open Set Filter Topology

""" + body + "end Checked.FalknerSkan.NegReversedWallShearRows\n"
(R / 'Checked/FalknerSkan/NegReversedWallShearRows.lean').write_text(out)
c = (R / 'Checked.lean').read_text()
for imp, after in (('import Checked.FalknerSkan.NegReversedWallShearRows\n', 'import Checked.FalknerSkan.NegReversedRows\n'),
                   ('import Checked.Trust.SecondReadingFSRevTable\n', 'import Checked.Trust.SecondReadingFSAttRows\n')):
    if imp not in c:
        assert after in c
        c = c.replace(after, after + imp, 1)
(R / 'Checked.lean').write_text(c)
h = (R / 'scripts/trust/headlines.txt').read_text()
if 'fs_neg_reversed_wall_shear_4_exists' not in h:
    if not h.endswith('\n'): h += '\n'
    h += ("# Falkner–Skan reversed-flow rows β = −0.04 … −0.09, −0.11 … −0.16 of Ganapol 2010 Table 7 (run 2026-11-13T0028Z; "
          "frozen cf66704 (run 2026-11-12T2228Z) and 33cd0de (row −0.15, run 2026-11-12T1828Z), proved on the reversed-flow "
          "stack generic in K, Checked/FSRev/; statements of the audited β = −1988/10000 reversed statement with β and window "
          "replaced; referee STANDS; β read blind in run 2026-11-13T0028Z)\n")
    for Nm, nm, tag, src in ROWS:
        h += f"Checked.FalknerSkan.NegReversedWallShearRows.fs_neg_reversed_wall_shear_{tag}_exists\n"
    (R / 'scripts/trust/headlines.txt').write_text(h)
L = (R / 'scripts/trust/literal_readings.txt').read_text()
S = 'Checked.Trust.SecondReading'
if 'fs_neg_reversed_wall_shear_4_exists' not in L:
    if not L.endswith('\n'): L += '\n'
    for Nm, nm, tag, src in ROWS:
        tail = f'{S}.fsRevRow{Nm}Rhs {S}.fskHalfLineTyped {S}.fskHalfLine {S}.fskWall {S}.fskEdge {S}.fsnDefectBelow {S}.stagSpeedBounded {S}.fsnWallValue'
        L += f'Checked.FalknerSkan.NegReversedWallShearRows.fs_neg_reversed_wall_shear_{tag}_exists {tail}\n'
    (R / 'scripts/trust/literal_readings.txt').write_text(L)
print('promoted')
