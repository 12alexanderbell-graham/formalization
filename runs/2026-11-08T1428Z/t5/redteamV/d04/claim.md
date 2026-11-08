# d04 (range of a certified number), F9 Consequence

False belief: The pole of the printed F(R0) expression is claimed to lie at Omega > 1, outside the physical range; certified pole is 0.538, inside (0,1).

Sentence misread: ...and a pole of the printed expression (at Omega > 1, outside the physical range 0 < Omega < 1), are certified in the block below...

Why checks accept: Only integers 0 and 1 and a relation sign are added; no certified value is repeated.

Adjacent block contradicts? Yes if compared: F9_pole block rounds the root to 0.538; the same section's Lean list says the printed relation is false at every Omega in (0,1).

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
