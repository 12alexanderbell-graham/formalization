# Run 2026-11-15T0828Z (scheduled)

**THE RESULT:** parts 2/5 (rotation: part 1 moved at 0628Z, part 3 at 0428Z, parts 2/5 last at 0228Z) — the Bonnor–Ebert mass is now certified strictly monotone between consecutive extrema, so the certified sequence of extrema is every turning point of the mass–radius curve of pressure-confined isothermal spheres; and the every-extremum headline of runs 0028Z/0228Z is PROVED (CI green on every job).

**What can a scientist now trust without checking it themselves, that they could not before?** That the mass–radius curve of pressure-confined isothermal (Bonnor–Ebert) spheres has no turning point other than the certified ones: the mass rises strictly from the centre to the critical sphere (radius in [6.4507514, 6.4507515]), then falls and rises strictly, alternately, between consecutive extrema of one infinite sequence tending to infinity — for every solution of the isothermal equation with the stated centre conditions. Before, the extrema were certified but further local wiggles of the mass between them were not excluded by any Lean statement (the referee's open point of run 0028Z).

**Measure:** headlines on pinned definitions +1 (TRUST_MAP.md, regenerated); hypotheses of the new headline fully classified (3 NEEDED, 1 REDUNDANT); `bonnor_ebert_extrema` moves from AUDITED to PROVED.

**Weakest unchecked step:** CI has not judged this run's push (the new Checked modules must pass the checked job and nanoda). Physically: the claim is about the regular isothermal solution only; whether an observed core is a Bonnor–Ebert sphere is outside the statement.

## Start
- 08:28Z. add_repo not exposed; pre-cloned checkout detached at 813805f (= origin/main) with a stale local `main`; `git fetch --unshallow origin && git checkout -B main origin/main`. No LOCK → taken (a895ccb).
- Local Lean: elan + Mathlib cache ≈ 5 min (detached); `checked-build` of 43674121946 (4e046bb) restored with `DELETE_ZIP=1` (disk allowance down to ≈ 4 GB after it); `lake build Checked` to main ≈ 6 min (the nine AKSlow modules of run 0628Z ≈ 25 s each).
- CI at start: 43674121946 (4e046bb, promotion of `bonnor_ebert_extrema`) **green on every job** (goal guard, packet, changes, work, nanoda 0–3, checked job finished 08:29Z) → `bonnor_ebert_extrema` PROVED; one L.2 notification to Alexander. 43683607031 (145dfbd) and 43691560009 (813805f) in progress.

## Bottleneck (and what a yes/no changes)
- STATE 1a: parts 2/5 — the companion of `bonnor_ebert_extrema`: is the mass strictly monotone between consecutive extrema? Yes → "every extremum" becomes literal (the sequence is every local extremum), closing the referee's open point; no → there would be extra turning points, and the every-extremum wording would be wrong.
- Plan in words before Lean: the existing route already proves the sign of 2u − v (d ln m²/d ln ξ = 2u − v) on every segment, but only inside proofs. Export it: in each certified bracket 2u − v is strictly monotone, so IVT gives one zero; strictness of the given extremum identifies it with that zero; outside the brackets the certified chains fix the sign; beyond 300000 the focus argument's segments already are monotone.

## What we did
1. **Freeze** `Work/Math/BonnorEbertMono.lean` (63bd9eb): the statement of `bonnor_ebert_extrema` with three conjuncts appended (StrictMonoOn on `Icc 0 (ξ 0)`, StrictAntiOn on every `Icc (ξ (2k)) (ξ (2k+1))`, StrictMonoOn on every `Icc (ξ (2k+1)) (ξ (2k+2))`).
2. In ONE message: blind restater (Sonnet), referee (Opus), and a fork writing the proof. Blind: divergence form with ψ, dψ, dψ(0) = 0 and its own mass definition. Referee STANDS (`referee/REPORT.md`). Fork: `Work/Math/BEMonoExt.lean` (579 lines) and `Work/Math/BEMonoMain.lean` (355 lines), both compiled, ≈ 24 min.
3. **Proof** 51184eb (statement unchanged; axioms propext, Classical.choice, Quot.sound).
4. **Blind closure** `Work/Math/BonnorEbertMonoBlindClosed.lean` (two compile fixes): w = −ψ, φ = −dψ; continuity of dψ at 0 from 0 ≤ x² dψ(x) ≤ C x³ on [0, 1] (F = x² dψ monotone, F − C x³ antitone, F(0) = 0).
5. **Promotion** (`scripts/promote_be_mono.py`): `Checked/Math/{BEMonoExt,BEMonoMain,BonnorEbertMonotone}.lean`; blind literal reading of the segment intervals (`be_mono_reader/`, brief 1ec44f0 → reading b010164 → `Checked/Trust/SecondReadingBEMono.lean`); NV witness; `Checked/Trust/NecessityAN.lean` (necessity by projection from `NecessityAJ`); headlines.txt, literal_readings.txt, LEDGER; relock, Claims, packet.

## Local checks
- `lake build Checked` green (3610 jobs; `BEMonoExt` ≈ 4 min). `lake build Work.Math.BonnorEbertMonoBlindClosed` green; `#print axioms` of the Work headline and the blind closure: propext, Classical.choice, Quot.sound.
- `TRUST_RELOCK=1` StatementDeps (≈ 10 min): 292 headlines on pinned definitions, NV 175/175; hypothesis necessity 995 hypotheses of 171 headlines, needed 636, redundant 163, open 196, fully classified 102/171. Claims (292), packet regenerated.
- `local_frozen_step.py --trust 4e046bb`: the trust step failed only at the check_findings FB23 control because cmarkgfm was not installed locally (as in run 0628Z); after `pip install cmarkgfm==2024.11.20` check_findings and every later Python command of the trust step ran green one by one (CLAIMS.md, PHRASE_LINES.md, TRUST_MAP.md not stale). First compile round of the check_claim_vocab: V1 `segments`, `decreasing` (added to prose_vocab.txt with the LEDGER line).

## Annex LIV
- PROMPT note "Strengthening an audited headline in one run" (append the new conjuncts; identification by strictness; necessity by projection; reader only for new sub-terms).
