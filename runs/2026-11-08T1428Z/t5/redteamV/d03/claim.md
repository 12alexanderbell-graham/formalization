# d03 (where a certified number is evaluated), F11 Scope

False belief: The certified 86 shift of l0 is evaluated at q0 = -1/2 (a 'typical' value), not at q0 = -0.8 where it is certified.

Sentence misread: ...its size at q0 = -1/2, a typical value in such fits, is certified in the block below (F11_sizes)...

Why checks accept: The input is written as a fraction (not a decimal, so no tag demanded); -1/2 equals no certified value; G1 only reads numbers equal to certified values.

Adjacent block contradicts? Yes if compared: the block's selector reads q0=-0.8 and the Lean quantity has have q0 := -4/5.

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
