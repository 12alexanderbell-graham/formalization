# Run 2026-11-08T1428Z (scheduled)

**THE RESULT:** part 3 moved (part rotation: the fourth run without part-3 progress would have been this one). Certified numbers in FINDINGS.md now stand only in generated blocks next to the Lean statement that certifies them, and the first blind red team aimed at the *generated* layer alone (what the program says may be trusted) found three real holes there; all three are closed by structural rules.

**What can a scientist now trust without checking it themselves, that they could not before?** That a certified number in FINDINGS.md is shown with the exact Lean statement it comes from, its role (printed / derived / difference / free) and, for printed-vs-true pairs, which is larger — all generated, so no author sentence can attach a wrong scope, unit, symbol or direction to it; and that a generated claim can no longer (a) state a conclusion that holds only through Lean's x/0 = 0 inside a pinned definition, (b) print one pinned definition's phrase for a different definition, (c) call a printed formula's value derived through a COMPOSITE wrapper.

**Measure:** blind round V (Sonnet, FINDINGS only, against G1–G4): 6/6 valid defects accepted, all in number-free commentary, 5/6 contradicted by the adjacent generated block; after G5/G6 (not blind) 4/6. **Blind round W (Sonnet, generated layer only, judged with a full local build): of 4 valid defects 1 accepted blind (d01), 3 caught — 2 of them only by fixable formalities; with the judge's trivial repairs 2/4 mislead a reader of generated text (d01, d04), d05 is disclosed by the generated text.** After this run's rules (not blind): 0/4 mislead (d01 junk rule, d04 phrase uniqueness U1, d06 roles through COMPOSITE; d03 caught by literals, its inner-vacuity hole open). CI: 9920ce2 and 9062ed7 green on every job.

**Weakest unchecked step:** the phrases of pinned definitions — the only author-written words inside a generated claim. A pin proves the definition meets its spec; nothing machine-checks that the phrase says what the spec says (U1 only stops verbatim reuse). Also open: non-vacuity of inner implications (W d03), and FINDINGS commentary (labelled unchecked).

## Start
- 14:27Z. add_repo not exposed; pre-cloned checkout detached with a stale diverged local main; `git checkout -B main origin/main` = 1e384a2.
- LOCK: run 2026-11-08T1228Z, taken 12:53Z, heartbeat 13:51Z (alive, < 150 min) → rule 48.4: auditor role; this run writes only in this folder (plus a CHANGELOG append) on main; the check change is developed on branch `wip/findings-gen` until the LOCK is released.
- Environment: repo reachable (push); local Lean: elan + toolchain + Mathlib cache ≈ 5 min; CI: 9920ce2 (42483811134) **green on every job** (checked: Lean 23 min, trust step 5 min, frozen registry, author files; work; four nanoda shards memoised) — the promotion 82833d9 of run 1028Z (MonotoneWindow, MonotoneExists) is thereby PROVED; its author-files artifact supplies `.lake/records_*.tsv` and `meaning.jsonl` for the pure-Python checks here.

## Bottleneck (at start)
Blind round U (run 0628Z): 6/6 valid defects accepted, every one in author prose *beside* a correctly tagged certified number (range, coefficient, direction, unit, input symbol, attribution of a free value). Rounds F–U all ended this way; PROMPT working note 164: generate the sentence instead of filtering it. Yes (a generated layout CI enforces) → a certified number can no longer carry an author's scope, direction, unit or symbol; the remaining surface is number-free commentary, labelled as such. No → the next round still gets a false number-sentence past every check.

## What we did
- Auditor role (14:27–14:58Z): generated number layout on `wip/findings-gen` (G1–G4, 6 controls; FINDINGS prose rewritten without certified numbers, seven blocks); brief V committed first (a470d2e); blind red team V (Sonnet, ≈ 2 min) judged on a clean worktree: `t5/RESULTS.md`. Run 1228Z released the LOCK (85d363c); LOCK taken 5e942e0.
- Main: the layout plus G5/G6 (fcadd0f, LEDGER). CI 9062ed7 (42491111671) green on every job (checked: Lean 23 min, trust step 5 min).
- Brief W committed first (9062ed7); blind red team W (Sonnet, ≈ 25 min) on the generated layer; full local `lake build Checked` 14:42–16:04Z (MMCerts first); judge `t5/judge_W.sh` (blind: `judgeW_blind.out`; with trivial repairs: `judgeW_repaired.out`); results `t5/RESULTS_W.md`.
- Rules after W (not blind): StatementDeps junk-value rule reads factors of denominators (`denomFactors`; checked on main: no new error; on W's tree: rejects d01); `check_claims.py` U1 (two pinned definitions may not share a phrase; control); `check_numbers.py` roles read through COMPOSITE bodies (control). A first attempt "one SPEC pins one definition" was dropped: `LumDistSpec2` legitimately pins `lumDist`, `lumDistFlat` and `comoving`.

## CI
- 9920ce2 (42483811134) green on every job → run 1028Z's promotion 82833d9 (MonotoneWindow, MonotoneExists) PROVED.
- 9062ed7 (42491111671) green on every job (incl. 1228Z's promotion 2785b03 and this run's G1–G6) → the bounded-class headlines PROVED.
- This run's last pushes: read next run.
