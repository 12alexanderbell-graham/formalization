# Run 2026-11-11T1228Z: build Work/FalknerSkan/Neg1988RevBlindClosed.lean from the blind text (verbatim) by
# inserting helper lemmas before the first blind theorem and replacing each `sorry` by a proof.
import re
b=open('runs/2026-11-11T1228Z/blind/Neg1988RevBlind.lean').read()
head='''import Mathlib
import Work.FalknerSkan.Neg1988Rev

/-!
# Falkner–Skan at β = −0.1988, reversed-flow branch: the blind restatement, closed (run 2026-11-11T1228Z)

The definitions and theorems below are the blind restater's text (Sonnet, from the claims in words only;
`runs/2026-11-11T1228Z/blind/Neg1988RevBlind.lean`, brief 579e291), copied verbatim by
`runs/2026-11-11T1228Z/scripts/close_blind.py` with the placeholder proofs replaced by proofs from
`Work.FalknerSkan.Neg1988Rev` (helper lemmas inserted before the theorems).
-/
'''
assert b.startswith('import Mathlib\n')
body=b[len('import Mathlib\n'):]
helpers=open('runs/2026-11-11T1228Z/scripts/close_blind_helpers.lean').read()
k=body.index('theorem blind_rev_window')
body=body[:k]+helpers+'\n'+body[k:]
proofs=dict(re.findall(r'-- PROOF (\w+)\n(.*?)\n-- END', open('runs/2026-11-11T1228Z/scripts/close_blind_proofs.lean').read(), re.S))
for name,pr in proofs.items():
    m=re.search(r'theorem '+name+r'.*?:= by\n  sorry', body, re.S)
    assert m, name
    seg=m.group(0)
    body=body.replace(seg, seg[:-len('\n  sorry')]+'\n'+pr)
assert 'sorry' not in body
open('Work/FalknerSkan/Neg1988RevBlindClosed.lean','w').write(head+body)
# verbatim check: every blind line occurs in the output in order
out=(head+body).split('\n'); i=0
for line in b.split('\n'):
    if line.strip()=='sorry': continue
    while i<len(out) and out[i]!=line: i+=1
    assert i<len(out), ('missing', line)
print('ok: every blind line copied verbatim, in order')
