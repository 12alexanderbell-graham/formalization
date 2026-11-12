# Red team AH report (witness layer of T2b). None of the six was built: no lake or lean was run.

Each defect adds one module `Checked/Trust/NecessityM<n>.lean`, one import line in Checked.lean and one line in
scripts/trust/headlines.txt. Each is a new wrapper headline. All necessity witnesses reuse proofs already in
NecessityB and NecessityD. The Lean was written blind. The most likely compile risk is d01 `_h3` (lemma names, `rw` on the redshift).

| id | category | one line | generated line a reader would misread | expected |
|----|----------|----------|----------------------------------------|----------|
| d01 | wrong-statement | Wrapper of `lookback_second_order` with an added conjunct `redshift a t0 t0 = 0`. Hypothesis `a t0 != 0` goes from REDUNDANT on main to NEEDED. The `restated` detector misses it because the conjunct is equivalent to the hypothesis, not defeq to it. | `LookbackZero.lookback_second_order_zero (4): needed 2, 3, 4; redundant 1` | ACCEPTED |
| d02 | unregistered-or-misregistered | Duplicate wrapper of `exists_unique_critical`. Its witnesses are the originals, so 5 NEEDED and 1 fully classified headline are counted twice (889/155, 419, 55/155). | `Chemistry.CubicEOSAgain.exists_unique_critical_again (5): needed 1..5` | ACCEPTED |
| d03 | weakened-statement | The assumption `deriv a t0 != 0` is hidden in a `Units R` binder. Neither the numbering nor necShape reaches it, and hypothesis 4 reads as a definition of H. | `LookbackUnit.lookback_second_order_unit (4): needed 2, 4; redundant 1, 3`, no shape entry | ACCEPTED |
| d04 | weakened-statement | The assumption `0 < 1+u+w` is carried as data `PLift (0 < ...)`, so it is not numbered. The headline shows one hypothesis, fully classified. | `CubicEOSLift.critCubic_existsUnique_lift (1): needed 1` | ACCEPTED |
| d05 | vacuous-or-trivial-statement | Two conditions merged into one set-membership hypothesis. numParts = 1, so there is no `bundled` entry and the headline counts as fully classified. | `CubicEOSRegion.critCubic_existsUnique_region (1): needed 1` | ACCEPTED, unless whnfR unfolds the membership; then N4 fails |
| d06 | misleading-record | One REDUNDANT hypothesis (`-2<u`) and one REDUNDANT part of another hypothesis (`-2<u`), jointly necessary. The "each alone, not together" label is only added within one list. | `(2): needed 1; redundant 2; parts of 1 (2) needed 2; parts of 1 (2) redundant 1` | ACCEPTED |

No defect needs a LEDGER line or a stage. None edits an existing Checked file that other modules import,
apart from the import line in Checked.lean.
