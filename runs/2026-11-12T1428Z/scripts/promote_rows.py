#!/usr/bin/env python3
"""Run 2026-11-12T1428Z: promote the attached Falkner–Skan rows β = −0.17, −0.18, −0.19 (the rows of Ganapol 2010
Table 6 read blind) from Work to Checked, in the pattern of runs/2026-11-11T1028Z/scripts/promote_n1988.py:
copies of Work/FSAtt/R<Row>{Lo,Hi,Core}.lean (namespace rename, number-free module docs), the headline module
Checked/FalknerSkan/NegWallShearRows.lean with the frozen statements verbatim (names changed only), the blind
reading copy, Checked.lean / Work.lean wiring, headlines, literal readings, NV witnesses. Idempotent guards."""
import re, pathlib
R = pathlib.Path(__file__).resolve().parents[3]
ROWS = [('Seventeen', 'seventeen', '17', 'fsAttThirdRhs', 'third-from-last'),
        ('Eighteen', 'eighteen', '18', 'fsAttSecondRhs', 'second-from-last'),
        ('Nineteen', 'nineteen', '19', 'fsAttLastRhs', 'last')]
def doc(kind, which):
    if kind == 'Lo':
        return f'Generated weighted one-sided cells for the clamped adverse-sign field at the scaled coefficient of the {which} row of the attached table read blind, below the wall-shear window: every solution of the clamped field shows the slow-approach event. Every numeric side condition is checked by kernel evaluation over the rationals, one declaration per segment.'
    if kind == 'Hi':
        return f'Generated weighted one-sided cells for the clamped adverse-sign field at the scaled coefficient of the {which} row of the attached table read blind, above the wall-shear window: every solution of the clamped field overshoots. Every numeric side condition is checked by kernel evaluation over the rationals, one declaration per segment.'
    return f'Falkner–Skan at the {which} row of the attached table read blind: the wall-shear window and the existence of a fast-approach solution from the two certified chains taken as hypotheses, with rational bounds of the square root of the scaled coefficient.'
mods = []
for Nm, nm, tag, rd, which in ROWS:
    for kind in ('Lo', 'Hi', 'Core'):
        m = f'R{Nm}{kind}'; mods.append(m)
        s = (R / f'Work/FSAtt/{m}.lean').read_text()
        s = s.replace('import Work.FSAtt.', 'import Checked.FSAtt.').replace('Work.FSAtt.', 'Checked.FSAtt.')
        assert 'import Mathlib\n' not in s and 'sorry' not in s and 'Work.' not in s, m
        s = re.sub(r'/-!.*?-/', '/-! ' + doc(kind, which) + f' Module `{m}`, promoted from `Work/FSAtt/{m}.lean`. -/', s, count=1, flags=re.S)
        (R / f'Checked/FSAtt/{m}.lean').write_text(s)
# headline module: frozen statements verbatim
w = (R / 'Work/FalknerSkan/AttachedRows.lean').read_text()
thms = ''
for Nm, nm, tag, rd, which in ROWS:
    a = w.index(f'/-- Falkner–Skan with β = −{tag}/100: if')
    b = w.index('/-- Falkner–Skan with β', w.index(f'theorem fs_att_{nm}_exists_decay'))
    t = w[a:b].replace('Work.FSAtt.', 'Checked.FSAtt.')
    t = t.replace(f'fs_att_{nm}_window', f'fs_neg_wall_shear_{tag}_window').replace(f'fs_att_{nm}_exists_decay', f'fs_neg_wall_shear_{tag}_exists_decay')
    thms += t
head = (R / 'Checked/FalknerSkan/NegWallShear.lean').read_text()
imports = head[:head.index('import Checked.')]
out = imports + ''.join(f'import Checked.FSAtt.{m}\n' for m in mods) + """
/-! Falkner–Skan with adverse pressure gradient at the last three rows of an attached wall-shear table read blind: the wall shear of every solution with positive second derivative that approaches the edge value faster than every exponential, and the existence of such a solution, one pair per row. Module `NegWallShearRows`, promoted from `Work/FalknerSkan/AttachedRows.lean` (theorems `fs_att_seventeen_window`, `fs_att_eighteen_window`, `fs_att_nineteen_window` and their existence companions there). -/

namespace Checked.FalknerSkan.NegWallShearRows

open Set Filter Topology

""" + thms + "end Checked.FalknerSkan.NegWallShearRows\n"
(R / 'Checked/FalknerSkan/NegWallShearRows.lean').write_text(out)
# blind reading copy (code verbatim, module doc number-free)
rdf = (R / 'runs/2026-11-12T1428Z/fsatt_reader/SecondReadingFSAttRows.lean').read_text()
rdf = re.sub(r'/-!.*?-/', '/-! Blind literal reading of three tabulated Falkner–Skan wedge rows with decelerating outer stream, copied from `runs/2026-11-12T1428Z/fsatt_reader/SecondReadingFSAttRows.lean` (code verbatim; module doc rewritten without numbers). Reader: an independent Sonnet subagent from the brief next to it alone; it derived the equation from the wedge-flow similarity variables, checked it with sympy and read the pressure-gradient parameters from a typeset crop of the table. -/', rdf, count=1, flags=re.S)
(R / 'Checked/Trust/SecondReadingFSAttRows.lean').write_text(rdf)
# Checked.lean
c = (R / 'Checked.lean').read_text()
if 'import Checked.Trust.SecondReadingFSAttRows\n' not in c:
    c = c.replace('import Checked.Trust.SecondReadingFSNearSep\n', 'import Checked.Trust.SecondReadingFSNearSep\nimport Checked.Trust.SecondReadingFSAttRows\n')
if 'import Checked.FalknerSkan.NegWallShearRows\n' not in c:
    c = c.replace('import Checked.FalknerSkan.NegWallShear\n', 'import Checked.FalknerSkan.NegWallShear\n' + ''.join(f'import Checked.FSAtt.{m}\n' for m in mods) + 'import Checked.FalknerSkan.NegWallShearRows\n')
(R / 'Checked.lean').write_text(c)
# headlines
h = (R / 'scripts/trust/headlines.txt').read_text()
if 'fs_neg_wall_shear_17_window' not in h:
    h += "# Falkner–Skan attached rows β = −0.17, −0.18, −0.19 (run 2026-11-12T1428Z; frozen 964c644/this run, proved in Work on the attached-flow stack generic in K, Checked/FSAtt/; statements of the audited β = −1988/10000 pair with β and a ten-decimal window replaced; referee STANDS-WITH-CORRECTIONS; the windows confirm Ganapol 2010 Table 6): wall-shear windows of the decay-class solutions, and existence\n"
    for Nm, nm, tag, rd, which in ROWS:
        h += f"Checked.FalknerSkan.NegWallShearRows.fs_neg_wall_shear_{tag}_window\nChecked.FalknerSkan.NegWallShearRows.fs_neg_wall_shear_{tag}_exists_decay\n"
    (R / 'scripts/trust/headlines.txt').write_text(h)
L = (R / 'scripts/trust/literal_readings.txt').read_text()
S = 'Checked.Trust.SecondReading'
if 'fs_neg_wall_shear_17_window' not in L:
    for Nm, nm, tag, rd, which in ROWS:
        L += (f'Checked.FalknerSkan.NegWallShearRows.fs_neg_wall_shear_{tag}_window {S}.{rd} {S}.fskHalfLineTyped {S}.fskHalfLine {S}.fskWall {S}.fskEdge {S}.fsnDefectBelow {S}.fsnWallValue\n'
              f'Checked.FalknerSkan.NegWallShearRows.fs_neg_wall_shear_{tag}_exists_decay {S}.{rd} {S}.fskHalfLineTyped {S}.fskHalfLine {S}.fskWall {S}.fskEdge {S}.fsnDefectBelow\n')
    (R / 'scripts/trust/literal_readings.txt').write_text(L)
W = (R / 'Checked/Trust/Witnesses.lean').read_text()
if 'fs_neg_wall_shear_17_window' not in W:
    W = W.replace('import Checked.FalknerSkan.NegWallShear\n', 'import Checked.FalknerSkan.NegWallShear\nimport Checked.FalknerSkan.NegWallShearRows\n', 1)
    blk = """/-! Falkner–Skan attached rows read blind from a table (run 2026-11-12T1428Z): the solution of each row's existence
headline satisfies every hypothesis of that row's wall-shear window. -/
"""
    for Nm, nm, tag, rd, which in ROWS:
        blk += f"""
theorem fs_neg_wall_shear_{tag}_window : nonvacuity% Checked.FalknerSkan.NegWallShearRows.fs_neg_wall_shear_{tag}_window := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, hpos, hdec⟩ :=
    Checked.FalknerSkan.NegWallShearRows.fs_neg_wall_shear_{tag}_exists_decay
  exact ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, hpos, hdec, trivial⟩
"""
    W = W.replace('end Checked.Trust.NV', blk + '\nend Checked.Trust.NV')
    (R / 'Checked/Trust/Witnesses.lean').write_text(W)
print('promoted', mods)
