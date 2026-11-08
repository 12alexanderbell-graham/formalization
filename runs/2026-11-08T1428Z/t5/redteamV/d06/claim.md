# d06 (sign relative to a printed (src) number), F10 Plain words

False belief: At Omega = 0.041 the correct eta20 (-0.249 certified) is said to agree in sign with the printed one (+0.15[src]); it has the opposite sign.

Sentence misread: ...the right numbers are smaller and, at Omega = 0.041[src], agree in sign with the printed ones.

Why checks accept: Sentence has only a [src] input and no certified number; the certified -0.249 is in the block, the printed +0.15 in an [src] prose line.

Adjacent block contradicts? Block does not contradict it directly (it lists only the correct values, negative); contradiction needs the Printed bullet (+0.15[src]) vs block (-0.249).

LEDGER_add: none

Checks:
```
$ scripts/trust/check_numbers.py  (exit 0)
check_numbers selftest: 28 controls, 0 failing
certified numbers (FINDINGS.md outside '## Candidates under verification'): 26 certified [✓], 13 quoted [src], 2 inputs [in], 2 unchecked [unc]; 43 tagged
$ scripts/trust/check_numbers.py --base d80f565  (exit 0)
check_numbers selftest: 28 controls, 0 failing
certified-number diff vs d80f565: 26 certified pairs before, 26 now, 0 removed or changed
$ scripts/trust/check_prose.py  (exit 0)
check_prose: 198 headlines, 137 definitions, 21 glossary terms; 0 new problems; 352 known gaps (prose_baseline.txt)
$ scripts/trust/precheck_citations.py  (exit 0)
precheck_citations: 0 suspected
```
