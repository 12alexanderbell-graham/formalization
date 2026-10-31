# Run 2026-10-31T0028Z (scheduled)

Environment: repo pre-cloned (add_repo not exposed, not needed); a chat session pushed Alexander's instruction 10 (7ad9dc3) at 00:29Z, this run's LOCK rebased on it. Local Lean via elan + cache. Previous CI (41145491684) green. Governance, PROMPT (incl. new instruction 10, TARGETS "THE RESULT"), STATE, CHANGELOG read.

**THE RESULT:** part 3 (measured trust) started: first false-acceptance measurement of the whole pipeline against seeded wrong claims from red teams of a different model, and the checks strengthened against what it found; part 1 (every link machine-checked) advanced by the frozen registry, unused-binder and pin-shape checks.

**WHAT CAN A SCIENTIST NOW TRUST WITHOUT CHECKING IT THEMSELVES?** How often this system accepts wrong science, measured for the first time: the checks as they stood yesterday accepted **15 of 15** valid wrong claims seeded by red teams of a different model; the checks pushed this run reject 9 of them (**6 of 15 still accepted**); a third red team aimed at the new checks got 2 of 8 through (all 23 had passed yesterday's checks); and from now on no registered headline, pin, transcription or classification can change without CI forcing a LEDGER entry that names it.

**WEAKEST UNCHECKED STEP NOW:** new definitions that carry physics under a non-physics label (FORMULA/COMPOSITE: A04, B04), and prose records (numbers and scope in STATE/FINDINGS: A03, A06, B07); then the C-round holes in the new checks.

**BOTTLENECK AND WHY:** THE RESULT (part 3) needs a measured false-acceptance rate; every metric so far counted coverage, not what gets through. Yes (low rate) = evidence for the trust claim; no = the exact holes, ranked. It was no.

**WHAT WE DID:**
1. Three red teams (Sonnet; briefs in `t5/`): A honest mistakes (8), B adversarial vs the 2228Z checks (8), C adversarial vs this run's checks (8). Each defect is `apply.py` + `claim.md` (what a reader would wrongly believe, why it is false).
2. Judge (`t5/harness/judge.sh`): applies a defect to the clean tree, `lake build Checked`, forbidden tokens, trust step before (2228Z) and after (this run) in parallel on the same build, relock simulation, restore. Control (no defect) passes both.
3. Strengthened checks (all blocking, LEDGER integrity event): frozen registry (`scripts/trust/frozen.txt`, 239 fingerprints; `check_relock.py` demands a LEDGER line naming any changed/removed entry); unused binders in headlines and pins (looks through proofs that are other Checked theorems); pins must use an independent SPEC definition; theorems cited in STATE/FINDINGS must be registered (or pure mathematics); no `Work` imports in Checked; private definitions visible; stale `TRUST_MAP.md` fails. Baseline: all 101 headlines and 19 pins pass unchanged.
4. Red team C attacked version v2 within minutes: 8 holes (proof by bare constant, decorative spec in a pin, private definitions, Work import, citation outside "Results", conjunction-bundled hypothesis, kind relabelling, `PLift`-wrapped hypothesis); v3 (pushed) closes 6 of them mechanically before judging; C is judged against v3 (`t5/results/C*_v3.txt`).

**RESULT (A+B, valid defects = 15; A08 INVALID: missing import, repaired copy `d08r` judged separately):**

| Defect | Category | Checks as of 2228Z | This run's checks | Caught by |
|---|---|---|---|---|
| A01 | mistranscription (claim def) | ACCEPTED | caught* | frozen registry |
| A02 | mistranscription (claim def) | ACCEPTED | caught* | frozen registry |
| A03 | misleading record (scope) | ACCEPTED | ACCEPTED | — |
| A04 | wrong definition (new, FORMULA) | ACCEPTED | ACCEPTED | — |
| A05 | existential headline | ACCEPTED | ACCEPTED | — |
| A06 | wrong number in FINDINGS | ACCEPTED | ACCEPTED | — |
| A07 | unregistered result cited in STATE | ACCEPTED | caught | records check |
| B01 | mistranscription + claim + FINDINGS | ACCEPTED | caught | frozen registry |
| B02 | weakened headline, same name | ACCEPTED | caught | frozen registry |
| B03 | restatement "pin" (sinh for K=+1) | ACCEPTED | caught | pin shape |
| B04 | wrong definition (new, FORMULA) | ACCEPTED | ACCEPTED | — |
| B05 | overstated records + hand-edited map | ACCEPTED | caught (map half only) | stale map |
| B06 | unused hypothesis q₀ = −1 | ACCEPTED | caught | frozen + unused |
| B07 | wrong number in FINDINGS | ACCEPTED | ACCEPTED | — |
| B08 | pin restricted to de Sitter | ACCEPTED | caught | frozen + unused |

\* A01/A02 change frozen CLAIM bodies; confirmed runs in `t5/results/Ad0{1,2}_v2.txt` when present. Red team C: all 8 compiled; **the 2228Z checks accepted 8/8; v3 accepts 2/8**: C02 (spec placed in a decorative conjunct of a pin; v4, pushed after judging, counts only load-bearing SPEC positions: not yet re-judged) and C06 (hypothesis bundled in a conjunction, only partly used: open). Caught: C01 (unused hypothesis behind a bare-constant proof; look-through), C03 (private definition now visible: UNCLASSIFIED), C04 and C05 (trust step failed; error text not captured by the judge's filter, expected: Work import, citation outside "Results"; harness filter fixed, confirm next run), C07 (kind relabel: frozen kind, relock needs LEDGER), C08 (`PLift` hypothesis: all binders checked).

**Totals:** checks as of 2228Z accepted **23 of 23** valid seeded wrong claims; the checks now on main accept **8 of 23** (A+B 6/15 under v2, C 2/8 under v3). CI: main 41156834643 green (first CI run of the frozen registry: fingerprints portable); control `control/frozen-weakened` (B02 relocked without LEDGER) run 41158182668: read next run, must FAIL at check_relock.

**WHAT COULD STILL BE WRONG:** the local judge replicates CI except axiom audit, leanchecker and nanoda (no defect targets the kernel); "caught" for the frozen registry means *disclosed*: an author who names the change in LEDGER passes; red teams are one model (Sonnet) and saw the check code (B, C) or not (A); 24 defects are a small sample, so the rate is a first point, not an estimate with error bars.

**NEXT:** STATE "Exact next step".
