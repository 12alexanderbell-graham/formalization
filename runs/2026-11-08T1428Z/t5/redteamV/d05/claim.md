# d05 (unit or scale), F8 Scope

False belief: Milne sizes (certified as percentages 0.56 and 6.7) are called parts per thousand, and the small-k fractional shift is called per cent.

Sentence misread: ...(F8_sizes): the two Milne figures are parts per thousand of the exact distance, the small-k figure is a relative shift in per cent.

Why checks accept: Words about units are author prose; the numbers are not in the sentence.

Adjacent block contradicts? Yes if compared: the block quotes 100 * ... for the Milne values (percent) and no factor 100 for k^2 z^4/120.

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
