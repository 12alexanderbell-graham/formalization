#!/usr/bin/env python3
"""Run 2026-11-26T1228Z: write Checked/FSSep/BlowSep.lean, the separation stack at the start (cS, 0, 0) with
cS = -1/1000 (blowing): mk_sep_blow_scratch.py (the suction port with f >= cS in place of f >= 0), then
blow_energy.py (energy H - (2K/1000) p antitone; hypothesis K <= 6 down the stack), then the namespace and module doc."""
import subprocess, pathlib, re
R = pathlib.Path(__file__).resolve().parents[3]
S = R / 'runs/2026-11-26T1228Z/scripts'
subprocess.run(['python3', str(S / 'mk_sep_blow_scratch.py')], check=True)
subprocess.run(['python3', str(S / 'blow_energy.py')], check=True)
s = (R / 'runs/2026-11-26T1228Z/lean/BlowSep.lean').read_text()
assert s.count('namespace Scratch.BlowSep') == 1 and s.count('end Scratch.BlowSep') == 1
s = s.replace('namespace Scratch.BlowSep', 'namespace Checked.FSSep.BlowSep').replace('end Scratch.BlowSep', 'end Checked.FSSep.BlowSep')
doc = ('/-! Falkner–Skan separation with blowing at the wall: the separation stack (`SFlow`, `SUnclamp`, `SAssemble`) '
       'ported to the start (cS, 0, 0) of the clamped adverse-sign field, cS minus one thousandth. The stream function is '
       'at least cS instead of non-negative, so the energy of the unclamping is corrected by a multiple of the velocity '
       '(the shear lies between zero and two), and the coefficient is at most six down the stack; the shooting core takes '
       'the two certified chain coefficients as parameters. Written by `runs/2026-11-26T1228Z/scripts/mk_sep_blow.py`. '
       'Module `BlowSep`. -/')
s = re.sub(r'/-!.*?-/', lambda m: doc, s, count=1, flags=re.S)
s = s.replace('/-- The suction value of the start, one thousandth. -/', '/-- The blowing value of the start, minus one thousandth. -/')
(R / 'Checked/FSSep/BlowSep.lean').write_text(s)
print('wrote Checked/FSSep/BlowSep.lean')
