#!/usr/bin/env python3
"""Run 2026-11-11T1828Z: promote the reversed-flow stack generic in K (Work/FSRev/*) and the β = −0.1988
reversed-flow trio (Work/FalknerSkan/Neg1988Rev.lean) to Checked. Copies by script (namespace rename, imports,
number-free module docs), writes the headline module with the frozen statements verbatim (names changed only),
copies the blind literal reading, registers headlines, literal readings, NV witnesses. Idempotent guards."""
import re, pathlib
R = pathlib.Path(__file__).resolve().parents[3]
MI = (R / 'Checked/FalknerSkan/NegWallShear.lean').read_text()
MATHLIB = MI[:MI.index('import Checked.')]
DOCS = {
 'RBase': 'Falkner–Skan adverse pressure gradient with a free scaled coefficient, the reversed-flow branch: the lower slow-approach event with the threshold valid for every coefficient at least five, the tube side property and the certified tube shape.',
 'RCell': 'Falkner–Skan adverse pressure gradient with a free scaled coefficient: checked weighted cells of the clamped field and the segment lemmas used by the reversed-flow chains.',
 'RInv': 'Falkner–Skan adverse pressure gradient with a free scaled coefficient at least five: invariance of the lower slow-approach region of the reversed-flow branch.',
 'RUnclamp': 'Falkner–Skan adverse pressure gradient with a free scaled coefficient: a reversed-flow trajectory of the clamped field with neither event never meets a clamp, so it solves the unclamped problem.',
 'RIdent': 'Falkner–Skan adverse pressure gradient with a free scaled coefficient: strict clamp enclosures on checked cells, and the identification of an unclamped solution with a clamped one that stays strictly inside the clamps.',
 'RAssemble': 'Falkner–Skan adverse pressure gradient with a free scaled coefficient at least five, the shooting argument of the reversed-flow branch: an overshoot chain below, a slow-approach chain above and a tube give a reversed-flow solution in the fast-approach class with its wall value between the two scaled wall values.',
 'R1988Over': 'Generated weighted one-sided cells for the clamped adverse-sign field at the scaled coefficient of the tabulated row next to separation, reversed-flow branch, below the window: every solution overshoots. Every numeric side condition is checked by kernel evaluation over the rationals.',
 'R1988Slow': 'Generated weighted one-sided cells for the clamped adverse-sign field at the scaled coefficient of the tabulated row next to separation, reversed-flow branch, above the window: every solution shows the lower slow-approach event. Every numeric side condition is checked by kernel evaluation over the rationals.',
 'R1988Tube': 'Generated weighted one-sided cells for the clamped adverse-sign field at the scaled coefficient of the tabulated row next to separation, reversed-flow branch: the tube around the window. Every numeric side condition is checked by kernel evaluation over the rationals.',
 'R1988Printed': 'Generated weighted one-sided cells for the clamped adverse-sign field at the scaled coefficient of the tabulated row next to separation, from a small ball of wall values around the printed reverse-flow value: the solution stays strictly inside the clamps and overshoots. Every numeric side condition is checked by kernel evaluation over the rationals.',
 'R1988PrintedEnd': 'Falkner–Skan at the scaled coefficient of the tabulated row next to separation, from the printed reverse-flow wall value: the end state of the printed-value chain, read from the range of the last checked cell.',
 'RGlobal': 'Falkner–Skan adverse pressure gradient with a nonnegative scaled coefficient: global continuation of a solution that has entered the energy well around the edge value with positive stream function, through a dissipative clamped field whose energy is nonincreasing and keeps every clamp inactive.',
 'RPrintedNV': 'Falkner–Skan at the tabulated row next to separation: the initial-value problem with the printed reverse-flow wall value has a solution on the whole half-line (the printed-value chain, its end state and the global continuation, scaled back).',
}
MODS = list(DOCS)
for m in MODS:
    s = (R / f'Work/FSRev/{m}.lean').read_text()
    s = s.replace('import Work.FSAtt.', 'import Checked.FSAtt.').replace('Work.FSAtt.', 'Checked.FSAtt.')
    s = s.replace('import Work.FSRev.', 'import Checked.FSRev.').replace('Work.FSRev.', 'Checked.FSRev.')
    assert 'import Mathlib\n' not in s, m
    assert 'sorry' not in s and 'Work.' not in s, m
    s = re.sub(r'/-!.*?-/', '/-! ' + DOCS[m] + f' Module `{m}`, promoted from `Work/FSRev/{m}.lean`. -/', s, count=1, flags=re.S)
    (R / 'Checked/FSRev').mkdir(exist_ok=True)
    (R / f'Checked/FSRev/{m}.lean').write_text(s)
# headline module
w = (R / 'Work/FalknerSkan/Neg1988Rev.lean').read_text()
body = w[w.index('theorem sqrtK_pos'):w.index('end Work.FalknerSkan.Neg1988Rev')]
NAMES = [('fs_neg1988_reversed', 'fs_neg_reversed_wall_shear_exists'),
         ('fs_neg1988_printed_reversed_overshoots', 'fs_neg_reversed_printed_overshoots'),
         ('fs_neg1988_two_decay', 'fs_neg_wall_shear_two_decay')]
for a, b in NAMES:
    assert a in body
    body = body.replace(a, b)
body = body.replace('Work.FSAtt.', 'Checked.FSAtt.').replace('Work.FSRev.', 'Checked.FSRev.')
assert 'Work.' not in body
out = MATHLIB + """import Checked.FalknerSkan.FSScale
import Checked.FSRev.RAssemble
import Checked.FSRev.R1988Over
import Checked.FSRev.R1988Slow
import Checked.FSRev.R1988Tube
import Checked.FSRev.R1988Printed
import Checked.FSAtt.N1988Core
import Checked.FSAtt.N1988Lo
import Checked.FSAtt.N1988Hi

/-! Falkner–Skan with the adverse pressure-gradient coefficient −1988/10000 (the tabulated row next to separation), reversed-flow branch: a solution with negative wall shear that approaches the edge value faster than every exponential, the overshoot of the initial-value problem started from the printed reverse-flow wall value, and two solutions with different wall shear in that class. Module `NegReversedWallShear`, promoted from `Work/FalknerSkan/Neg1988Rev.lean` (theorems `fs_neg1988_reversed`, `fs_neg1988_printed_reversed_overshoots`, `fs_neg1988_two_decay` there). -/

namespace Checked.FalknerSkan.NegReversedWallShear

open Set Filter Topology

""" + body + "end Checked.FalknerSkan.NegReversedWallShear\n"
(R / 'Checked/FalknerSkan/NegReversedWallShear.lean').write_text(out)
# blind literal reading copy
rd = (R / 'runs/2026-11-11T1828Z/fsrev_reader/SecondReadingFSRevPrinted.lean').read_text()
rd = re.sub(r'/-!.*?-/', '/-! Blind literal reading of the reverse-flow Falkner–Skan wall value printed by Fazio (his 2012 arXiv paper, version 1; typeset page seen), copied from `runs/2026-11-11T1828Z/fsrev_reader/SecondReadingFSRevPrinted.lean` (code verbatim; module doc rewritten without numbers). Reader: an independent Sonnet subagent from the brief committed alone before it in that folder. -/', rd, count=1, flags=re.S)
(R / 'Checked/Trust/SecondReadingFSRevPrinted.lean').write_text(rd)
# Checked.lean
c = (R / 'Checked.lean').read_text()
add_trust = 'import Checked.Trust.SecondReadingFSRevPrinted\n'
if add_trust not in c:
    assert 'import Checked.Trust.SecondReadingFSNearSep\n' in c
    c = c.replace('import Checked.Trust.SecondReadingFSNearSep\n', 'import Checked.Trust.SecondReadingFSNearSep\n' + add_trust)
blk = ''.join(f'import Checked.FSRev.{m}\n' for m in MODS) + 'import Checked.FalknerSkan.NegReversedWallShear\n'
if 'import Checked.FalknerSkan.NegReversedWallShear\n' not in c:
    assert 'import Checked.FalknerSkan.NegWallShear\n' in c
    c = c.replace('import Checked.FalknerSkan.NegWallShear\n', 'import Checked.FalknerSkan.NegWallShear\n' + blk)
(R / 'Checked.lean').write_text(c)
# headlines
h = (R / 'scripts/trust/headlines.txt').read_text()
if 'fs_neg_reversed_wall_shear_exists' not in h:
    h += ("# Falkner–Skan at β = −1988/10000, reversed-flow branch (run 2026-11-11T1828Z; frozen c9be92b and proved by run 1228Z in its runs/ folder, merged into Work and promoted by run 1828Z on the reversed-flow stack generic in K, Checked/FSRev/; blind restatement closed, referee STANDS-WITH-CORRECTIONS; candidate C-FS-1988R): a decay-class solution with f''(0) in (−0.00515743, −0.00515741) exists; the IVP from Fazio's printed −0.005158 overshoots f' = 1; two decay-class solutions with different wall shear\n"
          "Checked.FalknerSkan.NegReversedWallShear.fs_neg_reversed_wall_shear_exists\n"
          "Checked.FalknerSkan.NegReversedWallShear.fs_neg_reversed_printed_overshoots\n"
          "Checked.FalknerSkan.NegReversedWallShear.fs_neg_wall_shear_two_decay\n")
    (R / 'scripts/trust/headlines.txt').write_text(h)
L = (R / 'scripts/trust/literal_readings.txt').read_text()
S = 'Checked.Trust.SecondReading'
H = 'Checked.FalknerSkan.NegReversedWallShear'
if 'fs_neg_reversed_wall_shear_exists' not in L:
    L += (f'{H}.fs_neg_reversed_wall_shear_exists {S}.fsNearSepWedgeRhs {S}.fskHalfLineTyped {S}.fskHalfLine {S}.fskWall {S}.fskEdge {S}.fsnDefectBelow {S}.stagSpeedBounded {S}.fsnWallValue\n'
          f'{H}.fs_neg_reversed_printed_overshoots source=Fazio {S}.fsRevPrintedWallFazio\n'
          f'{H}.fs_neg_reversed_printed_overshoots {S}.fsNearSepWedgeRhs {S}.fskHalfLineTyped {S}.fskHalfLine {S}.fskWall {S}.fsRevPrintedWallFazio\n'
          f'{H}.fs_neg_wall_shear_two_decay {S}.fsNearSepWedgeRhs {S}.fskHalfLineTyped {S}.fskHalfLine {S}.fskWall {S}.fskEdge {S}.fsnDefectBelow {S}.stagSpeedBounded {S}.fsnWallValue\n')
    (R / 'scripts/trust/literal_readings.txt').write_text(L)
# NV witness for the overshoot statement (the other two are existence statements)
W = (R / 'Checked/Trust/Witnesses.lean').read_text()
if 'fs_neg_reversed_printed_overshoots' not in W:
    W = W.replace('import Checked.Trust.NonVacuity\n', 'import Checked.Trust.NonVacuity\nimport Checked.FalknerSkan.NegReversedWallShear\nimport Checked.FSRev.RPrintedNV\n', 1)
    W = W.replace('end Checked.Trust.NV', """/-! Falkner–Skan at the pressure-gradient coefficient −1988/10000 (run 2026-11-11T1828Z): the initial-value
problem with the printed reverse-flow wall value has a solution on the whole half-line
(`Checked.FSRev.RPrintedNV.printed_ivp_exists`), which meets every hypothesis of the overshoot statement. -/

theorem fs_neg_reversed_printed_overshoots :
    nonvacuity% Checked.FalknerSkan.NegReversedWallShear.fs_neg_reversed_printed_overshoots := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hq0⟩ := Checked.FSRev.RPrintedNV.printed_ivp_exists
  exact ⟨f, p, q, hf, hp, hq, hf0, hp0, hq0, trivial⟩

end Checked.Trust.NV""")
    (R / 'Checked/Trust/Witnesses.lean').write_text(W)
print('promoted', MODS)
