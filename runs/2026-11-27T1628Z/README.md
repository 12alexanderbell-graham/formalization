# Run 2026-11-27T1628Z (external test long run: target O open closures, then O56–O61)

**THE RESULT:** part 2 and part 3 (the trust system on AI-produced mathematics it did not make). The open closures
left by run 1428Z were written: O53 (Turing degree rigidity) 3/3, O54 (Kadison–Ringrose) for readers A and B, O55
(strong Kadison–Kastler) reader C. Then six more families of OpenAI's release were read blind by three models and
closed in Lean against the frozen statements: large prime gaps (O56), power-free polynomial values (O57), little
finitistic dimension (O58), generalized star height (O59), ordinary two-point correlations (O60, both challenges)
and the permanent's border determinantal complexity (O61). No statement mismatch was found. One reader misreading
was caught and proved harmless (O60, reader B).

**What can a scientist now trust without checking it themselves, that they could not before?** That the Lean
statements of O53, O56, O57, O59, O60 and O61 say what three independent blind readings of the papers say, at
every link closed here, and that O54, O55 and O58 do for the readers closed. Several links needed a proof rather
than a glance: an arbitrary enumeration of the primes equals `Nat.nth` (O56), root counts in `ZMod q` equal residue
counts and an unconditional Euler product gives the partial-product limit (O57), a frozen `sSup` density is a
`liminf` (O56), a misplaced complex conjugate is cancelled by the symmetry `t ↦ −t` (O60), and topological closures
of coefficient vectors are limits of sequences (O61).

**Weakest unchecked step:** no family of this run is DONE. Every closure was compiled only against this
repository's Mathlib; every replay at OpenAI's pin is dispatched and queued behind the judge's uncached build
(run 46020135102, building since 14:59Z).

## Start
- 16:28Z. Scheduled firing. No `LOCK`, no `EXTERNAL_LOCK` (run 1428Z released it): this run took `EXTERNAL_LOCK`
  (5c4b761) as the external test's long run (PROMPT 11).
- Env: repo ok (`add_repo` not exposed; the session clone was on a stale `main` whose commits are on origin; reset
  to origin/main). Local Lean installed by `scripts/start_run.sh` (elan, 4.35.0, Mathlib cache). openai/math
  cloned at the pin 3344da5 (`/home/claude/ext/oai`).
- CI: judge run 46020135102 (d50431d) still building Checked uncached (as run 1428Z expected, ≈ 250 min); every
  external dispatch queued behind it and behind the full re-replay 45956936114 (leanchecker shards still running).

## Target O (`validation/EXTERNAL_O.md`)
- Open closures of run 1428Z:
  - O53, Turing degrees: 3/3. `Set ℕ ≃ (ℕ → Bool)` carries each reader's reducibility to the frozen `Reduces`,
    so each reader's degree poset is order-isomorphic to the frozen `Degree` and rigidity transfers.
  - O54, Kadison–Ringrose: readers A and B. The frozen extra `[PartialOrder M] [StarOrderedRing M]` is supplied by
    Mathlib's spectral order; differentials proved equal. Reader C blocked: Mathlib has no `WStarAlgebra` instance
    for a von Neumann algebra on a Hilbert space (`EXTERNAL_BLOCKERS.md`).
  - O55, Kadison–Kastler: reader C closed (its commutant is `Set.centralizer` by `rfl`), so 3/3.
- New families (smallest remaining challenges first, by `family_map.py`; briefs 5dfa7d5 and da5a1fc, readings
  committed alone at 14b6065 and 9a09d32; readers A Opus, B Sonnet, C Haiku):
  - O56, prime gaps (doc 026): 6/6.
  - O57, power-free values (doc 020): 6/6. The frozen statement is Corollary 1.2 (every d ≥ 4). To check at the
    replay: the paper takes d ≥ 9 from Browning's theorem; the solution's 63 files name no such input.
  - O58, finitistic dimension (doc 198, two challenges): Theorem 1.1 and Corollary 1.2 (with both injective-
    generation sentences) for readers A and B. Reader C blocked: projective dimension by free resolutions has no
    Mathlib link to the Ext-based one. The two challenges define a constant of the same name; both are the true
    supremum on `WithBot ℕ∞`.
  - O59, generalized star height (doc 134): 3/3.
  - O60, two-point correlations (doc 007, two challenges): 9/9 against `OrdinaryTwoPointCorrelations` and Theorem
    1.2 3/3 against `OrdinaryElliott`. Reader B conjugated `χ(p)` but not `p^{it}`; proved harmless by symmetry.
  - O61, permanent (doc 108): 8/8 (Theorem 1.1 explicit and existential, exact dc). `SmoothInitialForm` (a lemma
    of the paper's body) not read; its proof is replayed only.
- Passed over: doc 126 (perfect matching: superpolynomial in Lean, exponential in the paper, disclosed).
- Readers' tool use: three readers report a refused Bash `grep` of Mathlib (Grep tool or own definitions instead).
- Dispatched replays: O-turing, O-hochschild, O-kadisonkastler (with closures; run 1428Z's dispatch 46029450827
  cancelled first); O-primegaps, O-powerfree, O-finitistic, O-finitistic-asym; O-starheight, O-elliott-twopoint,
  O-elliott-oe, O-permanent, O-permanent-initial.

## Annex LIV
- `scripts/external/compile_closure.sh`: local compilation of closures against frozen challenges outside the
  package root (the recipe was reinvented each run). PROMPT working note; LEDGER experiment.

## Next
- CI: read judge run 46020135102 and its shards ("restored the checked job's build"); then the queued external
  dispatches of this run and of run 1428Z (46020248291 … 46020286133, 46023625611, 46027208793). A closure that
  fails at OpenAI's Mathlib pin is a name change: fix it to elaborate at both pins.
- Read the S-cycleclique line: its replay job (140365540377) hit the job limit while nanoda ran (build saved for
  the next dispatch); leanchecker shard 4 (140508883565) failed, log not yet available.
- Open closures: O50 sharpness, O51 (TM2 composition), O52 reader C (word metric vs Cayley-graph walks), O54 and
  O58 reader C (blocked in Mathlib).
- Then target O from the next families by `family_map.py` (smallest first; candidates read but not started: 288
  Kadison similarity, 174 strong thin trees, 088 projection bodies, 072 Brennan).
