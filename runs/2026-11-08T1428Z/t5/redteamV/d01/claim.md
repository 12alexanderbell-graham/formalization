# d01 (records cited by the wrong name), F1 Plain words

False belief: Swapped record names: reader believes F1_l0 certifies the printed formula's value and F1_printedL0 the true l0.

Sentence misread: ...both values are certified in the block below: the printed formula's value (`F1_l0`) and the l0 of every flat LCDM model (`F1_printedL0`).

Why checks accept: Prose is outside the blocks; record names in code spans are not read by G1 (no tag, no number).

Adjacent block contradicts? Yes, if compared: the block shows F1_printedL0 = printedAvilesL0 (0.685) and F1_l0 = cosmoCoeff 5 (3.115).

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
