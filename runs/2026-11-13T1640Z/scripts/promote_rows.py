#!/usr/bin/env python3
"""Run 2026-11-13T1640Z: promote the attached Falkner–Skan rows β = −0.13, −0.14, −0.15, −0.16 (the first four rows of the
decelerating segment of Ganapol 2010 Table 6, read blind) from Work to Checked. Copy of
runs/2026-11-12T1428Z/scripts/promote_rows.py with the rows, the headline module (NegWallShearRowsTop), the reading copies
(rows 13/14/16: runs/2026-11-13T1640Z/fsatt_reader3; row 15: runs/2026-11-12T1428Z/fsatt_reader2) and the hypothesis-necessity
module NecessityX (hypotheses 1 and 3 NEEDED, 6 REDUNDANT, by the generic NecessityQ/NecessityR lemmas) added. Idempotent guards."""
import re, pathlib
R = pathlib.Path(__file__).resolve().parents[3]
# (Name, lower name, tag, reader constant, which, Work statement file)
ROWS = [('Thirteen', 'thirteen', '13', 'fsAttTopFirstRhs', 'first', 'AttachedRowsTop'),
        ('Fourteen', 'fourteen', '14', 'fsAttTopSecondRhs', 'second', 'AttachedRowsTop'),
        ('Fifteen', 'fifteen', '15', 'fsAttTopThirdRhs', 'third', 'AttachedRows'),
        ('Sixteen', 'sixteen', '16', 'fsAttTopFourthRhs', 'fourth', 'AttachedRowsTop')]
def doc(kind, which):
    if kind == 'Lo':
        return f'Generated weighted one-sided cells for the clamped adverse-sign field at the scaled coefficient of the {which} row of the decelerating segment of the attached table read blind, below the wall-shear window: every solution of the clamped field shows the slow-approach event. Every numeric side condition is checked by kernel evaluation over the rationals, one declaration per segment.'
    if kind == 'Hi':
        return f'Generated weighted one-sided cells for the clamped adverse-sign field at the scaled coefficient of the {which} row of the decelerating segment of the attached table read blind, above the wall-shear window: every solution of the clamped field overshoots. Every numeric side condition is checked by kernel evaluation over the rationals, one declaration per segment.'
    return f'Falkner–Skan at the {which} row of the decelerating segment of the attached table read blind: the wall-shear window and the existence of a fast-approach solution from the two certified chains taken as hypotheses, with rational bounds of the square root of the scaled coefficient.'
mods = []
for Nm, nm, tag, rd, which, wf in ROWS:
    for kind in ('Lo', 'Hi', 'Core'):
        m = f'R{Nm}{kind}'; mods.append(m)
        s = (R / f'Work/FSAtt/{m}.lean').read_text()
        s = s.replace('import Work.FSAtt.', 'import Checked.FSAtt.').replace('Work.FSAtt.', 'Checked.FSAtt.')
        assert 'import Mathlib\n' not in s and 'sorry' not in s and 'Work.' not in s, m
        s = re.sub(r'/-!.*?-/', '/-! ' + doc(kind, which) + f' Module `{m}`, promoted from `Work/FSAtt/{m}.lean`. -/', s, count=1, flags=re.S)
        (R / f'Checked/FSAtt/{m}.lean').write_text(s)
thms = ''
for Nm, nm, tag, rd, which, wf in ROWS:
    w = (R / f'Work/FalknerSkan/{wf}.lean').read_text()
    a = w.index(f'/-- Falkner–Skan with β = −{tag}/100: if')
    e = w.index(f'theorem fs_att_{nm}_exists_decay')
    b = w.find('/-- Falkner–Skan with β', e)
    if b < 0: b = w.index('end Work.FalknerSkan.', e)
    t = w[a:b].replace('Work.FSAtt.', 'Checked.FSAtt.')
    assert 'sorry' not in t
    t = t.replace(f'fs_att_{nm}_window', f'fs_neg_wall_shear_{tag}_window').replace(f'fs_att_{nm}_exists_decay', f'fs_neg_wall_shear_{tag}_exists_decay')
    thms += t.rstrip('\n') + '\n\n'
head = (R / 'Checked/FalknerSkan/NegWallShearRows.lean').read_text()
imports = head[:head.index('import Checked.')]
out = imports + ''.join(f'import Checked.FSAtt.{m}\n' for m in mods) + """
/-! Falkner–Skan with adverse pressure gradient at the first four rows of the decelerating segment of an attached wall-shear table read blind: the wall shear of every solution with positive second derivative that approaches the edge value faster than every exponential, and the existence of such a solution, one pair per row. Module `NegWallShearRowsTop`, promoted from `Work/FalknerSkan/AttachedRowsTop.lean` (theorems `fs_att_thirteen_window`, `fs_att_fourteen_window`, `fs_att_sixteen_window`) and `Work/FalknerSkan/AttachedRows.lean` (theorem `fs_att_fifteen_window`), with their existence companions there. -/

namespace Checked.FalknerSkan.NegWallShearRowsTop

open Set Filter Topology

""" + thms + "end Checked.FalknerSkan.NegWallShearRowsTop\n"
(R / 'Checked/FalknerSkan/NegWallShearRowsTop.lean').write_text(out)
# blind reading copies (code verbatim, module doc number-free)
for src, dst, n in (('runs/2026-11-13T1640Z/fsatt_reader3/SecondReadingFSAttRowsTop.lean', 'SecondReadingFSAttRowsTop', 'three'),
                    ('runs/2026-11-12T1428Z/fsatt_reader2/SecondReadingFSAttRowTop.lean', 'SecondReadingFSAttRowTop', 'one')):
    rdf = (R / src).read_text()
    rdf = re.sub(r'/-!.*?-/', f'/-! Blind literal reading of {n} tabulated Falkner–Skan wedge row{"s" if n != "one" else ""} with decelerating outer stream, copied from `{src}` (code verbatim; module doc rewritten without numbers). Reader: an independent Sonnet subagent from the brief next to it alone; it derived the equation from the wedge-flow similarity variables, checked it with sympy and read the pressure-gradient parameter{"s" if n != "one" else ""} from a typeset crop of the table. Rows are counted from the top of the cropped segment of the table, which holds the rows with decelerating outer stream. -/', rdf, count=1, flags=re.S)
    (R / f'Checked/Trust/{dst}.lean').write_text(rdf)
c = (R / 'Checked.lean').read_text()
if 'import Checked.Trust.SecondReadingFSAttRowsTop\n' not in c:
    c = c.replace('import Checked.Trust.SecondReadingFSAttRows\n', 'import Checked.Trust.SecondReadingFSAttRows\nimport Checked.Trust.SecondReadingFSAttRowsTop\nimport Checked.Trust.SecondReadingFSAttRowTop\n')
if 'import Checked.FalknerSkan.NegWallShearRowsTop\n' not in c:
    c = c.replace('import Checked.FalknerSkan.NegWallShearRows\n', 'import Checked.FalknerSkan.NegWallShearRows\n' + ''.join(f'import Checked.FSAtt.{m}\n' for m in mods) + 'import Checked.FalknerSkan.NegWallShearRowsTop\n')
if 'import Checked.Trust.NecessityX\n' not in c:
    c = c.replace('import Checked.Trust.NecessityW\n', 'import Checked.Trust.NecessityW\nimport Checked.Trust.NecessityX\n')
assert c.count('NegWallShearRowsTop') == 1 and 'NecessityX' in c and 'SecondReadingFSAttRowTop' in c
(R / 'Checked.lean').write_text(c)
h = (R / 'scripts/trust/headlines.txt').read_text()
if 'fs_neg_wall_shear_13_window' not in h:
    h += "# Falkner–Skan attached rows β = −0.13, −0.14, −0.15, −0.16 (run 2026-11-13T1640Z; frozen 67f8eef (−0.13, −0.14, −0.16) and 964c644 (−0.15), proved in Work on the attached-flow stack generic in K, Checked/FSAtt/; statements of the audited β = −1988/10000 pair with β and a ten-decimal window replaced; referees STAND (run 1640Z) and STANDS-WITH-CORRECTIONS (run 1428Z); the windows confirm Ganapol 2010 Table 6): wall-shear windows of the decay-class solutions, and existence\n"
    for Nm, nm, tag, rd, which, wf in ROWS:
        h += f"Checked.FalknerSkan.NegWallShearRowsTop.fs_neg_wall_shear_{tag}_window\nChecked.FalknerSkan.NegWallShearRowsTop.fs_neg_wall_shear_{tag}_exists_decay\n"
    (R / 'scripts/trust/headlines.txt').write_text(h)
L = (R / 'scripts/trust/literal_readings.txt').read_text()
S = 'Checked.Trust.SecondReading'
if 'fs_neg_wall_shear_13_window' not in L:
    for Nm, nm, tag, rd, which, wf in ROWS:
        L += (f'Checked.FalknerSkan.NegWallShearRowsTop.fs_neg_wall_shear_{tag}_window {S}.{rd} {S}.fskHalfLineTyped {S}.fskHalfLine {S}.fskWall {S}.fskEdge {S}.fsnDefectBelow {S}.fsnWallValue\n'
              f'Checked.FalknerSkan.NegWallShearRowsTop.fs_neg_wall_shear_{tag}_exists_decay {S}.{rd} {S}.fskHalfLineTyped {S}.fskHalfLine {S}.fskWall {S}.fskEdge {S}.fsnDefectBelow\n')
    (R / 'scripts/trust/literal_readings.txt').write_text(L)
W = (R / 'Checked/Trust/Witnesses.lean').read_text()
if 'fs_neg_wall_shear_13_window' not in W:
    W = W.replace('import Checked.FalknerSkan.NegWallShearRows\n', 'import Checked.FalknerSkan.NegWallShearRows\nimport Checked.FalknerSkan.NegWallShearRowsTop\n', 1)
    blk = """/-! Falkner–Skan attached rows read blind from the top of the decelerating segment of a table (run 2026-11-13T1640Z):
the solution of each row's existence headline satisfies every hypothesis of that row's wall-shear window. -/
"""
    for Nm, nm, tag, rd, which, wf in ROWS:
        blk += f"""
theorem fs_neg_wall_shear_{tag}_window : nonvacuity% Checked.FalknerSkan.NegWallShearRowsTop.fs_neg_wall_shear_{tag}_window := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, hpos, hdec⟩ :=
    Checked.FalknerSkan.NegWallShearRowsTop.fs_neg_wall_shear_{tag}_exists_decay
  exact ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, hpos, hdec, trivial⟩
"""
    i = W.rindex('end Checked.Trust.NV'); W = W[:i] + blk + '\n' + W[i:]
    (R / 'Checked/Trust/Witnesses.lean').write_text(W)
# necessity: hypotheses 1 and 3 NEEDED (NecessityQ profiles), 6 REDUNDANT (NecessityR.lim_one)
nx = """import Checked.Trust.NecessityQ
import Checked.Trust.NecessityR
import Checked.FalknerSkan.NegWallShearRowsTop

/-! Hypothesis necessity for the attached Falkner–Skan window headlines at the first four rows of the decelerating segment of a table read blind (run 2026-11-13T1640Z), by the profiles and the edge-limit lemma that serve the sibling rows: the Falkner–Skan equation and the relation between the stream function and the velocity are needed (explicit elementary profiles valid for every pressure-gradient coefficient), and the edge limit of the velocity is redundant (it follows from the other hypotheses for a decelerating stream). -/

namespace Checked.Trust.NCX

open Set Filter Topology Checked.Trust.NCQ Checked.Trust.NCS
"""
for Nm, nm, tag, rd, which, wf in ROWS:
    H = f'Checked.FalknerSkan.NegWallShearRowsTop.fs_neg_wall_shear_{tag}_window'
    nx += f"""
/-- The Falkner–Skan equation is needed in `fs_neg_wall_shear_{tag}_window`. -/
theorem fs_neg_wall_shear_{tag}_window_h3 : necessity% {H} 3 :=
  ⟨F, P, Q, hf_w, hp_w, F_zero, P_zero, P_lim, Q_pos, P_decay, notWin _ _ (by norm_num)⟩

/-- `f' = p` is needed in `fs_neg_wall_shear_{tag}_window`. -/
theorem fs_neg_wall_shear_{tag}_window_h1 : necessity% {H} 1 :=
  ⟨F1 (-{tag} / 100), P1 (-{tag} / 100), Q1 (-{tag} / 100), hp1 _, hq1 _ (by norm_num), F1_zero _,
    P1_zero _, P1_lim _ (by norm_num), Q1_pos _ (by norm_num), P1_decay _ (by norm_num),
    notWin1 _ _ _ (by norm_num)⟩

/-- The edge limit `p → 1` is redundant in `fs_neg_wall_shear_{tag}_window`. -/
theorem fs_neg_wall_shear_{tag}_window_r6 : dropped% {H} 6 := by
  intro f p q hf hp hq hf0 hp0 hpos hdec
  exact {H} f p q hf hp hq hf0 hp0
    (lim_one _ (by norm_num) f p q hf hp hq (fun η hη => (hpos η hη).le) hdec) hpos hdec
"""
nx += "\nend Checked.Trust.NCX\n"
(R / 'Checked/Trust/NecessityX.lean').write_text(nx)
print('promoted', mods)
