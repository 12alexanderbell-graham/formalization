# Run 2026-11-27T0628Z

**THE RESULT:** part 2 and part 3 (the trust system on AI-produced mathematics it did not make, and what its gates catch): target R (Alpöge's claimed proof of RH and GRH for Dirichlet L-functions) judged at statement level by three blind readers of three models with every reading closed in Lean, and both Sernau editions' proofs replayed (match, standard axioms, nanoda; leanchecker pending); target O (OpenAI's release): 37 families read blind and closed against their frozen statements, 3 DONE end to end, the headline missing from the Lean in one (O7), parts missing in eleven; two of our own findings wrong and struck through the same morning (missed challenges), with the tool that prevents it.

**What can a scientist now trust without checking it themselves, that they could not before?** That the five Lean headlines shared by all four editions of the RH/GRH archive (Alpöge 20 Nov, Sernau `grh` and `grh-compact` 25 Nov, the community copy) say exactly RH and GRH for all Dirichlet characters: ten blind readings (Opus, Sonnet, Haiku) of the note and the standard definitions are each proved equivalent to, or implied by, the frozen `Statements.lean` (standard axioms), Mathlib's ζ and L-functions are pinned as the unique continuations of their Dirichlet series, and the junk value at the pole is excluded. That both Sernau editions prove them with the standard axioms only, checked by an independent kernel (nanoda: 222,117 and 209,639 declarations), with every blind reading closed against each edition. And, for 37 families of OpenAI's release, which Lean statements carry their manuscripts' claims and which do not (`validation/EXTERNAL_O.md`): three families DONE end to end (O15 Littlewood, O17 Fourier L log L, O18 unit distances), the headline missing from the Lean in O7, a part missing in eleven (O3, O9, O10, O14, O19, O22, O24, O26, O31, O33, O36).

**Weakest unchecked step:** Lean's own replay (leanchecker) of the two Sernau editions, still running; the 20 November archive (175,187 modules, 17.4 M lines) cannot be replayed on this infrastructure (blocker R1).

## Start
- 06:28Z. Clone present at a detached head; local `main` was stale after a force-update of origin (860fd46 vs c6c79cf): `git checkout -B main origin/main`. No `LOCK`, no `EXTERNAL_LOCK`; PROMPT: target R top priority, then O, then M. `EXTERNAL_LOCK` taken bd4e9ce.
- Env: repo ok (`add_repo` not exposed; clone present, push works). elan installed (v4.35.0), Mathlib cache. CI via `external.yml` (dispatch with `only`). Two cores locally: every outside build goes to GitHub.
- Sources located with two web searches restricted to github.com/arxiv.org (titles only); primary sources downloaded from alpo.ge (note `remark.pdf`, archive parts 01–14, hashes equal to the mirror's published SHA-256) and github.com/lsernau/grh-lean (72fead1). No review, certification, dashboard, forum or news was opened.

## Target R — `validation/EXTERNAL_R.md`
- Statement **DONE**: brief da74d92 → readings 8458a7e (reader C's own compile fix committed alone) → closures 5c678d6: 10 readings closed (`R/closure/Closure.lean`, `Necessity.lean`, `Pins.lean`); Lean judge 45956936101 green on that commit.
- Coverage: "GRH" covers Dirichlet L-functions only; the note's "sign-only proof of Weil and Deligne" and "weakening of Vandiver" have no Lean statement; ERH only expected.
- Proof: escape scans of all three editions clean (no `sorry`, `axiom`, `native_decide`); replays `R-sernau-compact`, `R-sernau-grh` in run 45956936114; the original archive is blocker R1.
- Message to Alexander (L.2): statement verdict sent.

## Target O — `validation/EXTERNAL_O.md`
Ten families, smallest comparator challenge first, three blind readers each (Opus, Sonnet, Haiku), briefs committed before readers, readings committed alone:
O1 quasi-RH (editions differ 7/8 vs 11/12; Hecke link open), O2 Catalan (7/7), O3 Kaplansky char 2 (Theorem 1.1 closed; Gottschalk consequence has no Lean; replay PASSED: match, axioms, nanoda 82,359 declarations), O4 plane five-coloring (χ ≥ 6 closed; cited χ ≤ 7 uncovered), O5 Ostmann (7/7), O6 square-difference power saving (6/6), **O7 small Cohen–Macaulay (the Lean statement does not state the claim)**, O8 Falconer (3/3), O9 π exponent (μ = 2 closed for every reader; Flint–Hills uncovered), O10 explicit noncoordinate polynomial (corollary closed; the manuscript's explicit F, F(P) = −1 and ∇F(P) = 0 checked in Lean). Message to Alexander with the ten-family table sent.

## Target O, families O11–O25 (same protocol; briefs with exact paths and "no wildcards" from O14 on — no reader breach since)
O11 clique-free (3/3), O13 simple amenable (3/3), O14 sunflowers (3/7: explicit B_r uncovered), O15 Littlewood
(6/6 with the cited m_N ≥ 1 proved in Lean; **DONE**: replay and leanchecker 4/4), O16 dyadic (5/5), O17 Fourier
L log L (3/3), O18 unit distances (6/6), O19 F∞ (3/7: Corollary uncovered), O20 Mahler (3/6: equality case
uncovered), **O21 Euclidean Ramsey (the Classification theorem has no Lean statement)**, O22 circulant Hadamard
(3/6: Barker corollary only for even lengths), O23 Jacobsthal (6/6), O24 single-fold (3/6: corollary uncovered),
O25 lattice covering (3/3). Second challenges of O3, O8, O4 replayed. Message to Alexander with the table (O11–O22)
sent 10:30Z.

## General fixes (annex LIV; `scripts/external/`)
- `replay.sh`: modules resolve under the lakefile's `srcDir`; top-level `moreLeanArgs` carried over; outside packages of a closure required at the outside manifest's revisions, before Mathlib (OpenAI's quasi-RH, Catalan and Ostmann closures import PrimeNumberTheoremAnd, StrongPNT, rellich-kondrachov); `lake update` and build failures print their errors (three O-qrh jobs had ended silently).
- `coverage.py`: counts `def … : Prop` readings with their namespaces and closure statements naming them; reader-proved lemmas (no `sorry`) are not claims. Checked against every earlier family (same counts) and a negative control (0/10). Strips the `.` before a universe list (`type_of% @X.{u}`).
- `replay.sh`: applies the outside project's dependency patches (`patches/<pkg>-*.patch`, as OpenAI's lakefile does in `post_update`), recorded by hash; prints build errors; gives nanoda's worker threads a 1 GiB stack (the 32 MiB default overflowed on O-sqdiff).
- `scan_escapes.py`: `admit` reported apart from `sorry` (an identifier named `admit` gave 34 false hits).
- Lesson recorded: closures are written against our Mathlib but judged at the outside pin — O-amenable's closure printed `sorryAx` there and failed the job (the gate held); now written to elaborate at both pins. Challenges of one family can redeclare the same names (O21, O22, O23): one replay line per challenge.

## Target O, families O26–O37
O26 Steinitz–Bergström (8/11), O27 doubling Hilbert subset (4/6: reader B's closed-ball reading not implied — the
Lean fixes open balls), O28 Landau–Siegel zeros (4/4), O29 r(5,t) (6/6), O30 Hénon–Lane–Emden (6/6, corollary
derived in Lean), O31 separable quotient (1/6: (i) has no Lean statement), O32 Boone–Higman (3/4), O33 affine
cancellation (7/10: stable-coordinate corollary uncovered), O34 c₀ absorption (1/3), O35 Kaplansky odd
characteristic (4/4, p never evaluated), O36 Borsuk (closures not written), O37 infinite matroids (6/12: Theorem 1.1
closed; corollary challenge pending).
**Correction (11:07Z):** the O20 and O21 "no Lean statement" findings were ours and wrong (further challenges in
the same solution directory); withdrawn, Alexander told, `family_challenges.py` added, every other such finding
re-checked; reader A's Mahler equality and reader B's Ramsey Classification then closed against the missed
challenges.

## Next
- CI read first. Target R: run 45985482988 (R-sernau-grh, R-sernau-compact re-run so their leanchecker shards run;
  queued since 11:05Z behind the runner limit). Both shards sets green → target R proof verdict DONE for both
  Sernau editions (original archive NOT DONE, R1); then read the published checks (Lean FRO / Mathlib Initiative
  certification of 21 Nov, Sutherland's Comparator passes) and record what each found that the other did not; message
  Alexander. A red shard → the first failing module.
- Target O CI, runs 45973479628 … 45999181830: record each line's replay and leanchecker in `EXTERNAL_O.md`; a family
  is DONE when its coverage is COMPLETE and its replay and all four leanchecker shards pass (candidates: O2 Catalan,
  O5 Ostmann, O8 Falconer, O11, O13, O16, O23, O25, O28, O29, O30, O35). Re-dispatch `O-matroid` (its line now
  carries the closure; the queued run 45999181830 predates it).
- Target O closures not written: O20 B and C equality (Hanner transport to `Fin n → ℝ`), O21 A and C Classification
  (coefficient-field transport) and (i)/(ii), O34 A and B (c₀ ⊆ ℓ^∞ ≅ `C₀(ℕ, ℝ)`), O36 Borsuk (Frobenius matrices ≅
  `EuclideanSpace ℝ (Fin 4 × Fin 4)`), O37 Corollary 1.4 (second challenge), O31 B and C (ii), O32 A's
  every-generating-set form, O26 the every-constant form.
- Then target O families 38+ by challenge size (`family_challenges.py` for every family first), then target M.
