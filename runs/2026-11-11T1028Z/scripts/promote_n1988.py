#!/usr/bin/env python3
"""Run 2026-11-11T1028Z: promote the attached-flow stack generic in K (Work/FSAtt/*) and the β = −0.1988 pair
(Work/FalknerSkan/Neg1988.lean) to Checked. Copies by script (namespace rename, imports), writes the headline
module with the frozen statements verbatim, copies the blind literal reading, registers headlines, the literal
reading line, NV witnesses, the open-necessity disclosure; wires Checked.lean / Work.lean. Idempotent guards."""
import re, pathlib, sys
R = pathlib.Path(__file__).resolve().parents[3]
DOCS = {
 'ABase': 'Falkner–Skan adverse pressure gradient with a free scaled coefficient and a positive wall value: the slow-approach event with the threshold valid for every coefficient at least five, and the certified chain shape from a start with zero position and velocity.',
 'AFlow': 'Falkner–Skan adverse pressure gradient with a free scaled coefficient: the global flow of the clamped field from a start with zero position and velocity, continuous in the wall value (Lipschitz bound, norm bound and uniqueness from the separation flow module).',
 'AUnclamp': 'Falkner–Skan adverse pressure gradient with a free scaled coefficient at least five: a slow-approach or no-event trajectory of the clamped field never meets a clamp, so it solves the unclamped problem.',
 'AAssemble': 'Falkner–Skan adverse pressure gradient with a free scaled coefficient at least five, the shooting argument on the scaled problem: openness and disjointness of the two event sets, a wall value in neither, and the solution it gives.',
 'AWindow': 'Falkner–Skan adverse pressure gradient with a free scaled coefficient at least five: two certified chains (slow approach below, overshoot above) give a fast-approach solution with its wall shear between the two scaled wall values, and the same window for every fast-approach solution.',
 'N1988Lo': 'Generated weighted one-sided cells for the clamped adverse-sign field at the scaled coefficient of the tabulated row next to separation, below the wall-shear window: every solution of the clamped field shows the slow-approach event. Every numeric side condition is checked by kernel evaluation over the rationals, one declaration per segment.',
 'N1988Hi': 'Generated weighted one-sided cells for the clamped adverse-sign field at the scaled coefficient of the tabulated row next to separation, above the wall-shear window: every solution of the clamped field overshoots. Every numeric side condition is checked by kernel evaluation over the rationals, one declaration per segment.',
 'N1988Core': 'Falkner–Skan at the tabulated row next to separation: the wall-shear window and the existence of a fast-approach solution from the two certified chains taken as hypotheses, with rational bounds of the square root of the scaled coefficient.',
}
MODS = ['ABase', 'AFlow', 'AUnclamp', 'AAssemble', 'AWindow', 'N1988Lo', 'N1988Hi', 'N1988Core']
for m in MODS:
    s = (R / f'Work/FSAtt/{m}.lean').read_text()
    s = s.replace('import Work.FSAtt.', 'import Checked.FSAtt.').replace('Work.FSAtt.', 'Checked.FSAtt.')
    assert 'import Mathlib\n' not in s, m
    assert 'sorry' not in s, m
    # module doc: number-free (check_prose rule 7), says where it was promoted from
    s = re.sub(r'/-!.*?-/', '/-! ' + DOCS[m] + f' Module `{m}`, promoted from `Work/FSAtt/{m}.lean`. -/', s, count=1, flags=re.S)
    (R / 'Checked/FSAtt').mkdir(exist_ok=True)
    (R / f'Checked/FSAtt/{m}.lean').write_text(s)
# headline module
w = (R / 'Work/FalknerSkan/Neg1988.lean').read_text()
thm = w[w.index('/-- Falkner–Skan with β = −1988/10000: if'):w.index('end Work.FalknerSkan.Neg1988')]
thm = thm.replace('Work.FSAtt.', 'Checked.FSAtt.').replace('fs_neg1988_window', 'fs_neg_wall_shear_window').replace('fs_neg1988_exists_decay', 'fs_neg_wall_shear_exists_decay')
head = (R / 'Checked/FalknerSkan/NegWindow.lean').read_text()
imports = head[:head.index('import Checked.')]
out = imports + """import Checked.FSAtt.N1988Core
import Checked.FSAtt.N1988Lo
import Checked.FSAtt.N1988Hi

/-! Falkner–Skan with the adverse pressure-gradient coefficient −1988/10000 (the tabulated row next to separation): the wall shear of every solution with positive second derivative that approaches the edge value faster than every exponential, and the existence of such a solution. Module `NegWallShear`, promoted from `Work/FalknerSkan/Neg1988.lean` (theorems `fs_neg1988_window`, `fs_neg1988_exists_decay` there). -/

namespace Checked.FalknerSkan.NegWallShear

open Set Filter Topology

""" + thm + "end Checked.FalknerSkan.NegWallShear\n"
(R / 'Checked/FalknerSkan/NegWallShear.lean').write_text(out)
# blind literal reading copy
rd = (R / 'runs/2026-11-11T1028Z/fsw_reader2/SecondReadingFSNearSep.lean').read_text()
rd = re.sub(r'/-!.*?-/', '/-! Blind literal reading of a tabulated Falkner–Skan wedge row with decelerating outer stream, copied from `runs/2026-11-11T1028Z/fsw_reader2/SecondReadingFSNearSep.lean` (code verbatim; module doc rewritten without numbers). Reader: an independent Sonnet subagent from the brief next to it alone; it derived the equation from the wedge-flow similarity variables and read the pressure-gradient parameter from the typeset arXiv page. -/', rd, count=1, flags=re.S)
(R / 'Checked/Trust/SecondReadingFSNearSep.lean').write_text(rd)
# Checked.lean
c = (R / 'Checked.lean').read_text()
add_trust = 'import Checked.Trust.SecondReadingFSNearSep\n'
if add_trust not in c:
    c = c.replace('import Checked.Trust.SecondReadingFSSepW\n', 'import Checked.Trust.SecondReadingFSSepW\n' + add_trust)
blk = ''.join(f'import Checked.FSAtt.{m}\n' for m in MODS) + 'import Checked.FalknerSkan.NegWallShear\n'
if 'import Checked.FalknerSkan.NegWallShear\n' not in c:
    c = c.replace('import Checked.FalknerSkan.NegWindow\n', 'import Checked.FalknerSkan.NegWindow\n' + blk)
(R / 'Checked.lean').write_text(c)
# Work.lean
wl = (R / 'Work.lean').read_text()
for m in MODS:
    if f'import Work.FSAtt.{m}\n' not in wl:
        wl = wl.replace('import Work.FalknerSkan.Neg1988\n', f'import Work.FSAtt.{m}\nimport Work.FalknerSkan.Neg1988\n')
if 'import Work.FalknerSkan.Neg1988BlindClosed\n' not in wl:
    wl = wl.replace('import Work.FalknerSkan.Neg1988\n', 'import Work.FalknerSkan.Neg1988\nimport Work.FalknerSkan.Neg1988BlindClosed\n')
(R / 'Work.lean').write_text(wl)
# headlines
h = (R / 'scripts/trust/headlines.txt').read_text()
if 'fs_neg_wall_shear_window' not in h:
    h += ("# Falkner–Skan at β = −1988/10000, the tabulated row next to separation (run 2026-11-11T1028Z; frozen 50de3b1 by run 0828Z, proved in Work and promoted by run 1028Z on the attached-flow stack generic in K, Checked/FSAtt/; blind restatement closed, referee STANDS-WITH-CORRECTIONS; candidate C-FS-1988): the wall shear of the decay-class solution lies in (0.0052181, 0.0052182), and such a solution exists\n"
          "Checked.FalknerSkan.NegWallShear.fs_neg_wall_shear_window\nChecked.FalknerSkan.NegWallShear.fs_neg_wall_shear_exists_decay\n")
    (R / 'scripts/trust/headlines.txt').write_text(h)
# literal readings (same shape as the β = −1/10 lines, with the new wedge reading)
L = (R / 'scripts/trust/literal_readings.txt').read_text()
S = 'Checked.Trust.SecondReading'
if 'fs_neg_wall_shear_window' not in L:
    L += (f'Checked.FalknerSkan.NegWallShear.fs_neg_wall_shear_window {S}.fsNearSepWedgeRhs {S}.fskHalfLineTyped {S}.fskHalfLine {S}.fskWall {S}.fskEdge {S}.fsnDefectBelow {S}.fsnWallValue\n'
          f'Checked.FalknerSkan.NegWallShear.fs_neg_wall_shear_exists_decay {S}.fsNearSepWedgeRhs {S}.fskHalfLineTyped {S}.fskHalfLine {S}.fskWall {S}.fskEdge {S}.fsnDefectBelow\n')
    (R / 'scripts/trust/literal_readings.txt').write_text(L)
# NV witness
W = (R / 'Checked/Trust/Witnesses.lean').read_text()
if 'fs_neg_wall_shear_window' not in W:
    W = W.replace('import Checked.Trust.NonVacuity\n', 'import Checked.Trust.NonVacuity\nimport Checked.FalknerSkan.NegWallShear\n', 1)
    W = W.replace('end Checked.Trust.NV', """/-! Falkner–Skan at the pressure-gradient coefficient −1988/10000 (run 2026-11-11T1028Z): the solution of
`Checked.FalknerSkan.NegWallShear.fs_neg_wall_shear_exists_decay` satisfies every hypothesis of the wall-shear window. -/

theorem fs_neg_wall_shear_window : nonvacuity% Checked.FalknerSkan.NegWallShear.fs_neg_wall_shear_window := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, hpos, hdec⟩ :=
    Checked.FalknerSkan.NegWallShear.fs_neg_wall_shear_exists_decay
  exact ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, hpos, hdec, trivial⟩

end Checked.Trust.NV""")
    (R / 'Checked/Trust/Witnesses.lean').write_text(W)
print('promoted', MODS)
