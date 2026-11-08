# Run 2026-11-08T0028Z (scheduled)

**THE RESULT:** part 3 moved (measured trust / every link machine-checked): a certified number in FINDINGS.md is now bound by machine to the quantity and argument Lean certifies it for — selectors generated from the Lean records, checked tags (S1–S4, P1–P2) and a generated table of all 26 certified values — closing the open defect class of blind round T (d01). The Hiemenz trio of run 2228Z read PROVED (CI 42427258702 green on every job).

**What can a scientist now trust without checking it themselves, that they could not before?** That a certified number in FINDINGS.md belongs to the argument, parameter slot and quantity its tag names — e.g. that 0.56 % is the Milne error at z = 1 and 6.7 % at z = 2, that −0.249 is the η₂₀ coefficient at Ω = 0.041 — because CI now rejects a tag or a prose `z = …` that disagrees with the Lean statement, and the exact certified quantity is printed next to every value in a generated table. And that the Hiemenz wall-shear window is PROVED (strict library, CI and nanoda green).

**Measure:** open class of round T d01 closed (the swap is rejected in three forms: values swapped, tags forged, tags stripped); adversary (Sonnet) against the first version (S1–S3): 7/7 defects accepted; after S4, P1, P2 (not blind): 5/7 accepted, all of the *role* kind. Selector baseline: 2 records (shrink-only). Checked headlines 188 (unchanged), NV 123/123.

**Weakest unchecked step:** the *role* prose gives a certified number — "true" vs "printed", which record, which symbol a value is (adversary d1, d2, d5, d6) — is still free author text; the generated table makes it checkable by a reader, not by CI.

## What we did
- Start: LOCK (f6df076); elan + Mathlib cache; full `lake build Checked` started first (00:30–01:29Z).
- Design: a `RoundsTo x d k` conjunct's *selector* = program-definition head of `x`, its numeral arguments by binder, and `let v := c` arguments inside `x` (so a record can name its evaluation point without a new definition and its evidence label). `F8_sizes` and `F11_sizes` restated with `let`s, literal order chosen so the literal_baseline line only loses literals.
- `scripts/trust/StatementDeps.lean`: `roundsSel`, `posRoundsToSels`, `posRoundsToXs`; `ratLits` reads `let` values; `.lake/records_numbers.tsv` gets selector and quantity columns.
- `scripts/trust/check_numbers.py`: S1 (tag selector = conjunct selector), S2 (multi-valued records must name the selector; shrink-only `records_selector_baseline.txt`: F9_values, F10_exceptions), S3 (prose `v = c` agrees with the nearest selector tag), S4 (argument values only in that form), P1/P2 (input tags name the parameter slot when a record fixes several; slots from `fixed` in `.lake/meaning.jsonl`), `--selftest` (11 controls, run first), generated section `## Certified numbers (generated from the Lean records; do not edit)` (`--write`; stale = error). FINDINGS tags updated (no value changed).
- Adversary (Sonnet, pure-Python snapshot of S1–S3, ≈ 1 min): `adversary/` (REPORT.md, d1–d7 diffs and claims). Then S4 and P1/P2 written after reading it (not blind).
- Local: StatementDeps with relock (188 headlines, NV 123/123), Claims regenerated, every Python trust check green, base checks against 5556e24 green (check_relock, check_numbers --base with the LEDGER line), make_packet --check, goal guard, precheck_citations, status lines, prose controls.
- Records: STATE (last updated, trust-track bullet, Hiemenz PROVED in its section and Results, environment, daily review, exact next step), LEDGER, CHANGELOG, BLUEPRINT, TARGETS part 3, PROMPT working note.

## Adversary results (`adversary/`)
| defect | BLIND (S1–S3) | AFTER (S1–S4, P1–P2; not blind) |
|---|---|---|
| d1 F1 true/printed values swapped (two single-valued records) | accepted | accepted (role) |
| d2 F2_toy true/printed swapped, tags kept | accepted | accepted (role) |
| d3 F2_toy parameters permuted (w₀ ↔ wₐ) | accepted | caught: P2 (bare tags), P1 (swapped slot tags) |
| d4 F8 redshifts swapped as "at redshift 2 … 1" | accepted | caught: S4 |
| d5 F9_values true/printed swapped (baselined record) | accepted | accepted (role) |
| d6 F3 "+0.24 at q₀ = −0.55" → "−0.55 at q₀ = +0.24" | accepted | accepted (role: which symbol a value is) |
| d7 F8 range stated as "up to redshift 1" (record at z = 2; weaker, arguably true) | accepted | accepted |

## CI
- 5556e24 (42427258702, Hiemenz promotion): green on every job (checked: Lean step 29 min, trust step, frozen registry, author files; work; nanoda shards 12–19 min). Hiemenz trio PROVED.
- 24caf5b (42427418841): cancelled by coalescing (records only).
- f6df076 (42429893051), dce69bf, 12da5ad, ef070d8 and the records commit: read next run.

## Start
- 00:28Z: pre-cloned shallow checkout detached; `git merge --ff-only origin/main` refused (unrelated histories in the shallow clone), `git checkout -B main origin/main` = 24caf5b. add_repo not exposed. No LOCK; taken in f6df076.
