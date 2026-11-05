# Run 2026-11-05T1628Z (scheduled)

**THE RESULT:** part 3 (measured trust) by rotation (idle since 0828Z): a second, independent blind red team K — 6/6 wrong claims accepted by the checks on main; measured blind against the rules run 1428Z wrote meanwhile (4/6 still accepted); four more rules close all six; plus a CI robustness repair (three checked jobs lost without a log today).

**What can a scientist now trust without checking it themselves, that they could not before?** That what CLAIMS.md prints is what Lean proved: no Checked module can change how statements are printed (a global unexpander turned every `≤` into `<` in 146 claims, unnoticed by every check); that a binder in a claim is named after the pinned slot it fills unless it only adds digits, subscripts or primes (`Ωde` for the matter fraction now prints as `Ω`); that a COMPOSITE label is neither an alias carrying a name (`qNought := cosmoCoeff 2`, which is −q₀) nor a structure with a free formula in its fields; and that a source a headline names ("Planck 2018") is the source of a transcription the statement actually reaches.

**Weakest unchecked step:** whether the "blind" second formulations and readings were written blind (disclosed in LEDGER, not machine-checked); then CLAIMs without numerals (no second reading needed) and arithmetic glue in COMPOSITE bodies without numerals.

**Kind of result:** measurement (blind false acceptance: 6/6 against main, 4/6 against run 1428Z's new rules) plus strengthening (0/6 after, not blind).

## Start
- 16:28Z: LOCK of run 1428Z (14:28Z, 120 min old, < 150) → auditor role (48.4): writes only this folder and a CHANGELOG append until the lock is stale (16:58Z) or released. Run 1428Z had pushed only its LOCK commit 01b0c8c.
- add_repo not exposed; pre-cloned detached HEAD, stale local main reset to origin/main (01b0c8c). Local Lean: elan installer accepted, Mathlib cache; `lake build Checked` 16:33–17:20Z (detached).
- Auditor role used for the blind red team K (Sonnet, brief `t5/briefK.md` = the 0828Z brief with snapshot cb0223f; read-only worktree, output outside the repo, copied to `t5/redteamK/`): 6 defects in 17 min.
- 16:58Z: run 1428Z's LOCK 150 min old with nothing pushed after it → treated as dead (48.4), takeover recorded; this run's LOCK 090aa41. Run 1428Z was in fact alive (a 90-min local build) and pushed its own round K and five rules at ≈ 17:00Z, append-only, leaving STATE to this run. Its rules and this run's overlapped (both wrote a `claim_baseline.txt` and a "rule 8"); the merge kept all of run 1428Z's rules and added this run's four distinct ones on top (this run's first commit was rebuilt on origin/main; nothing of 1428Z's was discarded).

## CI read
- Promotion 6a32db1, CI 42039795953: **success** (all jobs) — `pr_omega1_unique`, `pr_omega1_exists` **PROVED**. Records 46a759e 42040438574 green.
- 01b0c8c (1428Z LOCK) 42045496695: **checked job lost 1.5 min into the build** (log 404) — third runner loss today (ff010a6, 70d33e3 in nanoda).
- This run: cb0223f 42065458336, 090aa41 42069964094, **85619a0 (swap repair) 42070074021 green on every job**; 1428Z's 2b56945 42070285492 and d675e9f 42070370128 green; 52459ff (merged rules) 42079443594 and the records commit: read next run.

## Work
1. **CI repair** (annex LIV, LEDGER experiment): checked job frees preinstalled toolchains, adds an 8 GB swap file before the build and prints `df`/`free` around nanoda. No check changed.
2. **Blind red team K** (`t5/redteamK/`, all six compile): printer hijack by a global `@[app_unexpander LE.le]` (d01), inline mistranscribed CLAIM s₀ = 1 − 9Ω (d02), COMPOSITE alias `qNought := cosmoCoeff 2` documented as q₀ (d03), binder `Ωde` for the matter fraction (d04), Prop structure `IsBoyleTemperature` with 2a/(RT) labelled COMPOSITE (d05), invented "Planck 2018" Ω = 0.265 (d06).
3. **Judge** (`t5/judge_K.sh`, worktree, all six combined, full CI replica): **6/6 ACCEPTED at 85619a0**; **4/6 ACCEPTED blind against run 1428Z's rules** (d02 and d06 rejected).
4. **Four rules** (LEDGER): StatementDeps — no unexpander/delaborator active for importers and no meta-level code in Checked (except NonVacuity); COMPOSITE/CLAIM body rules read structures (orders erased); COMPOSITE aliases rejected. Claims.lean — binder decorations digits/subscripts/primes only. check_prose rule 9 — sources must be the source of a reached transcription. **After: 0/6** (d04 reads correctly). Main: StatementDeps green (165 headlines, NV 106/106), check_prose 0 new, CLAIMS.md (`vc` → `v` in four claims) and packet regenerated, every `--base` check green.

## Measurement
| | before | after |
|---|---|---|
| Blind round K (this run's six), valid defects accepted | 6/6 (main at 85619a0); 4/6 (run 1428Z's rules) | 0/6 (merged rules, not blind) |
| Round K in all (both red teams) | 12/12 accepted at the old checks | 0/12 |
| Checked modules able to change the printer of CLAIMS.md | any | none (blocking) |
| Checked jobs lost without a log today | 3 | swap + resources printed; evaluate over the next ten pushes |

## Next step
See STATE.md "Exact next step" (next run: part 1 or 2).
