Category: scope-extension via a numeral outside S3/S4 pattern ('redshift 5', not bound value)
Reader would wrongly believe: The 1.3e-5 bound (certified at z=2 only) holds up to z=5; actually z⁴ grows 39x at z=5 (about 5e-4).
Sentence misread: relative shift k²z⁴/120 ≤ 1.3×10⁻⁵[✓F8_sizes(k=0.01, z=2)] up to redshift 5
Why accepted: S4 only flags numerals equal to a bound value (2); S3 needs 'z = c'. Free role: no R-rule.
Checks (run from copy; git worktree base ac435db worked):
certified numbers (FINDINGS.md outside '## Candidates under verification'): 28 certified [✓], 13 quoted [src], 15 inputs [in], 2 unchecked [unc]; 58 tagged
certified-number diff vs ac435db: 38 certified pairs before, 38 now, 0 removed or changed
check_prose: 192 headlines, 137 definitions, 21 glossary terms; 0 new problems; 352 known gaps (prose_baseline.txt)
precheck_citations: 0 suspected
