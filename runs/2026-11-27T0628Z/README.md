# Run 2026-11-27T0628Z (external test: target R, then target O)

**THE RESULT:** part 2 and part 3 (the trust system on AI-produced mathematics it did not make, and what its gates catch): target R (Alpöge's claimed proof of RH and GRH for Dirichlet L-functions) judged at statement level by three blind readers of three different models with every reading closed in Lean; target O (OpenAI's release) started, ten families judged, one Lean statement found not to state its manuscript's claim.

**What can a scientist now trust without checking it themselves, that they could not before?** That the five Lean headlines shared by all four editions of the RH/GRH archive (Alpöge 20 Nov, Sernau `grh` and `grh-compact` 25 Nov, the community copy) say exactly RH and GRH for all Dirichlet characters: ten blind readings (Opus, Sonnet, Haiku) of the note and the standard definitions are each proved equivalent to, or implied by, the frozen `Statements.lean` (standard axioms), Mathlib's ζ and L-functions are pinned as the unique continuations of their Dirichlet series, and the junk value at the pole is excluded. And, for ten families of OpenAI's release, which Lean statements carry their manuscripts' claims and which do not (`validation/EXTERNAL_O.md`).

**Weakest unchecked step:** whether the proofs are sound: the replays of the two Sernau editions (match against the frozen challenge, axioms, nanoda, leanchecker) were still running at the end of the session's record (run 45956936114); the 20 November archive (175,187 modules, 17.4 M lines) cannot be replayed on this infrastructure (blocker R1).

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

## General fixes (annex LIV; `scripts/external/`)
- `replay.sh`: modules resolve under the lakefile's `srcDir`; top-level `moreLeanArgs` carried over; outside packages of a closure required at the outside manifest's revisions, before Mathlib (OpenAI's quasi-RH, Catalan and Ostmann closures import PrimeNumberTheoremAnd, StrongPNT, rellich-kondrachov); `lake update` and build failures print their errors (three O-qrh jobs had ended silently).
- `coverage.py`: counts `def … : Prop` readings with their namespaces and closure statements naming them; reader-proved lemmas (no `sorry`) are not claims. Checked against every earlier family (same counts) and a negative control (0/10).

## Next
- CI read first: run 45956936114 (R-sernau-compact, R-sernau-grh; then their leanchecker shards). Green → target R proof verdict for the Sernau editions DONE (original archive stays NOT DONE, R1); then read the published checks (Lean FRO / Mathlib Initiative certification, Comparator passes) and record what each found that the other did not. Red → the first failing step; a build failure of the edition is a finding, ours a blocker.
- Target O replays: 45961122008 (O-catalan), 45963613011 (O4–O6), 45966220553 (O7–O9), 45966290931 (O-qrh-zeta, rebuilding with error printing: three `RellichKondrachov` modules failed to build in run 45962257301), 45967351577 (O-noncoord); then re-dispatch O-qrh-dirichlet and O-qrh-hecke. Update each verdict in `EXTERNAL_O.md`.
- Target O open links worth a general tool: the Hecke character correspondence (O1), Isbell's 7-coloring (O4, cited), MvPolynomial `pderiv` vs the real-function gradient (O10).
- Then target O families 11–13 (next challenges by size: CliqueFreeLog, PlaneColoring, SimpleAmenable), then target M.
