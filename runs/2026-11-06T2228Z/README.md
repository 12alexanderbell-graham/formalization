# Run 2026-11-06T2228Z (scheduled)

**THE RESULT:** part 3 (measured trust): reader-facing paraphrases moved from deny-lists to an allow-list — a headline's paraphrase in CLAIMS.md may now only use the words and numbers of its own generated claim, function words and a disclosed vocabulary; junk-value conclusions and status prose that claims "checked" without naming a Checked headline are rejected. Blind red teams judged: P 6/6 accepted by the round-O rules, 0/6 after; Q 3/6 accepted by the first version of the new rules, 0/6 after the tightening (AFTER columns not blind; `t5/RESULTS.md`).

**What can a scientist now trust without checking it themselves, that they could not before?** That the paraphrase printed under a headline in CLAIMS.md introduces no word the generated claim lacks except those in one public vocabulary file (empty today), and no number the statement does not contain: before this run, any English word outside six deny-lists passed ("implies … exactly one solution", "for the full duration of the run", "an inverted potential has a vanishing natural frequency").

**Measure:** blind false acceptance: round P 6/6 (round-O rules), round Q 3/6 (first version of this run's rules; the three rejections from older checks); after this run's final rules 0/6 and 0/6, not blind. Paraphrase words outside the generated claim: 1133 existing keys baselined (shrink-only), new ones 0. Headlines whose conclusion is a Mathlib junk value: 0 (rule new).

**Weakest unchecked step:** paraphrases that reorder the claim's own words (red team Q d04: quantifier order "there is n … for every E" over ∀E ∃n) — no rule reads word order; and the Thomas–Fermi promotion awaits its CI (42304551583).

## Start
- 22:28Z: pre-cloned checkout detached at 1414e21 with a stale diverged local main; `git reset --hard origin/main` = 1414e21. add_repo not exposed.
- LOCK: still tracked at 1414e21 although that commit (run 2026-11-06T2028Z records) says "remove LOCK" — the deletion was never staged. The holder's records are complete, so this run treated the lock as released and took it (fe7ac97). Root cause fixed: goal guard (42f90df, narrowed in e72d899 after its own message tripped it).
- Local Lean: elan installer accepted, Mathlib cache fetched (≈ 2 min). Full `lake build Checked` started 22:34Z (MMCerts first), ≈ 90 min.
- CI read: 3147cbb 42280355291 green on every job (nanoda 105 min). 1414e21 42304551583 (Thomas–Fermi promotion) in progress — read next run.

## Work
1. **Bottleneck** (STATE next step 2, part 3 due): red team P's six defects. Before judging, the pattern: rounds F, G, J, N, O, P each defeated a deny-list with an unlisted word. A yes (an allow-list that rejects P's prose defects without rejecting genuine paraphrases) changes the class from "vocabulary race" to "reviewed vocabulary"; a no would mean paraphrases must go (generated text only).
2. **Rules** (e72d899, written after reading P — not blind): `scripts/trust/check_claim_vocab.py` V1–V5, `scripts/trust/check_status_lines.py`, W2 over namespaces; CI wired; baseline of the existing tree.
3. **Blind red team Q** (Sonnet, brief `t5/briefQ.md` committed 336fca2 before it ran, snapshot e72d899, 6.5 min): 6 defects in `t5/redteamQ/` — status prose without the word PROVED; x/0 through a hypothesis `mass = 0`; `deriv |x| 0 = 0`; quantifier order swapped using the theorem's own name words; "settled at equilibrium" through a disclosed vocabulary addition; "to 6 decimal places" over `RoundsTo … 3`.
4. **Rules tightened after reading Q** (not blind): the theorem's name and binder names are no longer claim words; V6 numerals; V5 `deriv` without differentiability and zero-divisor variables; S1 reads any status claiming checked/promoted/verified/certified/CI green; long-time words (settle, converge, asymptotic, eventual, final) barred from the vocabulary; CLAIMS.md notation states Mathlib's total-function conventions. Baseline regenerated 985 → 1133 (stricter rules, existing headlines only; LEDGER).
5. **Judging** (after the LOCK release, worktrees with a copy of this run's build): P 6/6 accepted BEFORE, 0/6 AFTER; Q 3/6 accepted BEFORE (blind; d02 caught by the round-K junk rule, d03 and d06 by check_literals), 0/6 AFTER. The judge found a V6 bug (10⁴ read as 104), repaired c99eb45. Table: `t5/RESULTS.md`.

## Notes
- Q d04 (quantifier order) stays open: the allow-list bounds the words, not their arrangement. The structural answer would be to show only generated text to readers; recorded as the next decision if rounds keep passing paraphrase defects.
