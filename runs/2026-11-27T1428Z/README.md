# Run 2026-11-27T1428Z (external test long run: the CI queue blocker, then target O from O44)

**THE RESULT:** part 2 and part 3 (the trust system on AI-produced mathematics it did not make, and the
infrastructure that judges it). First, the judge had stopped working: since 10:45Z no judged push could go green,
and the external replays sat queued for four hours. This run found the cause and repaired it. Then nine more
families of OpenAI's release were read blind by three models and closed in Lean against the frozen statements:
Seymour's second-neighbourhood conjecture, Kaplansky's zero-divisor counterexample, the Gaussian moat, the
logarithmic Brunn–Minkowski inequality, Tingley's problem and the sensitivity/block-sensitivity separation (O44–O49).
Three more were read (O50–O52). No statement mismatch was found.

**What can a scientist now trust without checking it themselves, that they could not before?** That the Lean
statements of O44–O49 say what three independent blind readings of the papers say, at every link closed here.
Two of those links needed a junk-value check rather than an assumption: a real-valued volume could hide an infinite
Wulff body (proved bounded), and a frozen `dist` in ℂ had to equal the readers' distances (proved). O44 is closed in
both directions. For O49, the abstract's "fixed α > 2" claim has no comparator challenge. It is closed instead against
the solution's own theorem, read here. Also, the judge can again finish on an uncached build, and external builds no
longer evict its cache.

**Weakest unchecked step:** no family of this run is DONE. Every closure was compiled only against this repository's
Mathlib. Every replay at OpenAI's pin is dispatched but not yet read. O49's fixed-α closure was compiled locally
against a stub of the solution theorem, so its axioms are standard only once the replay builds it.

## Start
- 14:28Z. Scheduled firing. No `LOCK`, no `EXTERNAL_LOCK`: this run took `EXTERNAL_LOCK` (9be9e17) as the external
  test's long run (PROMPT 11; queue R → O → M → item 2 → item 3).
- Env: repo ok (`add_repo` not exposed; the session clone was present on a stale `main` whose commits are all on
  origin/main; reset to origin/main). Local Lean installed by `scripts/start_run.sh` (elan, 4.35.0, Mathlib cache).
  openai/math cloned at the pin 3344da5.

## The CI blocker (LEDGER: two integrity entries, 39.5; PROMPT working note)
- Symptom: at 14:30Z all ten Lean jobs of judge run 45984094021 (868eee2) had been in their `lean-action` step
  since 10:45–11:05Z, and 13 external dispatches had been queued since 10:22Z.
- First change (36e1b95): the nanoda and leanchecker shards now wait for the checked job and restore its packed
  build (`checked-build`, the same commit) instead of each rebuilding all of Checked.
- Cause (read in the log of checked job 140457035518 once it was cancelled at 240 min): `Cache not found` for the
  lake cache, and the build was still running at module 3639 of 3862. So the job was building, not hung. About
  thirty external lines had each saved their closure build to the 10 GB Actions cache and evicted the judge's
  lake cache.
- Second change (d50431d): external builds now reach their leanchecker shards as artifacts. The cache is written
  only for unfinished replays. The checked job's timeout went from 240 to 350 min.
- Cancelled:
  - Judge runs whose checked job could not finish: 45984094021, 45992056288, 45993219893, 46007920072, 46017116416.
  - External dispatches that had not started under the old workflow: 45985457433, 45987645772, 45988801441,
    45991304112, 45993856973, 45994140108, 45999181830, 46003398573, 46008329252, 46011205856, 46019774641.
  - The full re-replay that this run's own workflow push triggered by mistake: 46020135368.
- Their lines were re-dispatched under the new workflow: 46020248291 … 46020286133 (seven runs). This covers every
  O line from O23 to O46 that was waiting, plus O-sqdiff.
- Left running: 45985482988 (target R leanchecker), 45982423945, 45981618513, 45973479628.

## Target O, O44–O52 (`validation/EXTERNAL_O.md`)
- Process: `family_map.py` first; briefs 0ed6b5c, 7bfe069 and 44efa61; readings committed alone (2dc1534, 9426459,
  54a69e17). Readers: A (Opus), B (Sonnet), C (Haiku).
- Skipped: 066 (37 lines). Its only challenge is a lemma stated with the release's own definitions, and its headline
  is disclosed as outside the Lean.
- Results:
  - O44, Seymour: 3/3 in both directions; orientation shown necessary.
  - O45, Kaplansky zero divisors: Theorem 1.1 3/3; "conjecture false" 3/3; "Moreover" (finite 2-dimensional
    K(G,1)) 1/3. A's form (higher homotopy groups vanish) and C's form (simplicial complex) need theory Mathlib
    lacks.
  - O46, Gaussian moat: 3/3 on each of its three claims.
  - O47, log Brunn–Minkowski: Theorem 1.1 3/3. Corollary 1.2 (L_p) has no Lean statement.
  - O48, Tingley: 3/3.
  - O49, sensitivity: both sentences of Theorem 1.1 3/3. The abstract's fixed-α claim is 3/3 against
    `fixed_power_separation`.
  - O50, Gaussian propeller: the inequality 3/3. Mathlib had no theorem that `stdGaussian` on ℝ^d has the
    density (2π)^{-d/2}e^{-‖x‖²/2}, which all three readers wrote. It was recorded as a blocker and then proved
    in this run (`stdGaussian_eq_withDensity`, by characteristic functions; standard axioms). The sharpness
    sentence is not closed.
  - O51, superstring: no closure. Linking the readers' input encodings to the frozen one needs composition of
    polynomial-time TM2 machines, which Mathlib lacks (blocker).
  - O52, torsion-free hyperbolic group: reader A closed. Reader B's reading is proved false in Lean: B read
    "within that distance of the other two sides" as near both sides, and that bounds every word length.
- Our own defects:
  - The O44 brief's excerpt ended one line before the directed-triangle sentence.
  - Reader C wrote its O47–O49 files under the wrong directory names (moved unchanged).
- Dispatched replays: O-seymour, O-zerodiv, O-moat (46020286133); O-logbm, O-tingley, O-sensitivity (46023625611);
  O-propeller, O-superstring, O-hyperbolic (dispatched after 69aa930; an earlier dispatch without O50's closure,
  46026591992, was cancelled).
- Alexander was messaged at about 15:20Z with the O38–O49 table and the CI repair.

## Next
- CI:
  - Read judge run 46020135102 (d50431d). Its checked job builds uncached once (≈ 250 min), then saves the lake
    cache. Check that the shards print "restored the checked job's build".
  - Read the external dispatches 46020248291 … 46020286133 and the O-logbm/O-tingley/O-sensitivity dispatch. In
    particular, check that leanchecker shards print `build artifact: success`.
  - Read the target R leanchecker run (45985482988).
  - A closure that fails at OpenAI's Mathlib pin is a name change; fix it to elaborate at both pins.
- Open closures: O50 sharpness (sectors equal up to null rays), O51 (TM2 composition), O52 reader C (word metric).
- Then target O from 295 (Kadison–Ringrose), 241 (Turing degrees) and 289 (Kadison–Kastler), smallest first, by
  `family_map.py`. Then target M.
