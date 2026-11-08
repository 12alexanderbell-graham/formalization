Category: wrong formula coefficient in prose (untagged integer)
Reader would wrongly believe: The l₀ shift is 105q₀⁴ (which would be -43, not -86); true shift is 210q₀⁴ as Lean-certified -86.
Sentence misread: absorbed exactly by l₀ ↦ l₀ − 105q₀⁴ (≈ −86[✓F11_sizes(q₀=−0.8)] ...
Why accepted: Integers are not numbers to the checker; the certified -86 still matches its tag.
Checks (run from copy; git worktree base ac435db worked):
certified numbers (FINDINGS.md outside '## Candidates under verification'): 28 certified [✓], 13 quoted [src], 15 inputs [in], 2 unchecked [unc]; 58 tagged
certified-number diff vs ac435db: 38 certified pairs before, 38 now, 0 removed or changed
check_prose: 192 headlines, 137 definitions, 21 glossary terms; 0 new problems; 352 known gaps (prose_baseline.txt)
precheck_citations: 0 suspected
