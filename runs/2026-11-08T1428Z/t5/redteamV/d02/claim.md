# d02 (direction of an error), F2 Propagation

False belief: Printed l0 is too large by 2(1-Om)(7-Om)wa^2 (true: printed is smaller; true - printed = +2.345 at the block's point).

Sentence misread: ...gets it too large by 2(1-Omega_m)(7-Omega_m)w_a^2 (one instance, certified in the block below, F2_error).

Why checks accept: Direction words are not read near a record name without a number; the number 2 is an integer coefficient, not equal to a certified value.

Adjacent block contradicts? Yes: F2_error is cosmoCoeff - printed = 2.345 > 0, and the F2_toy order line says printed is below derived; also the Correct bullet says printed - true = -2(...).

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
