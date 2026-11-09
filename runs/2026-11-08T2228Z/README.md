# Run 2026-11-08T2228Z (scheduled)

**THE RESULT:** part 3 — the words that tell a scientist *which argument is which* in a generated claim (observation vs emission time, which species, which rate constant), the sign conventions and the qualifiers of each pinned quantity now come from blind readers of the specifications and are bound by CI slot by slot; measured by blind red team Z in the same run. Side result for parts 2/5 (scratch, compiled): the upper half of the class −1 ≤ f' ≤ 1 in the Hiemenz/Homann theorems is automatic.

**What can a scientist now trust without checking it themselves, that they could not before?** That in every generated claim each argument of a pinned definition is introduced by the role a blind reader of its specification gave it (a claim can no longer silently call the emission time the observation time, or the complex the product), that each sign convention a blind reader found (curvature parameter = minus Ω_k, de Sitter has negative Ricci scalar, …) is stated word for word, and that each pinned quantity carries its blind name with every restricting qualifier ("flat ΛCDM Friedmann expansion law").

**Measure (blind red team Z on the phrase layer):** brief 0234518 committed alone, snapshot 5dfc17e, six defects committed 7754ecc before judging. As submitted against the snapshot's rules: **6/6 pass** (sign deletion, time-role swap, species permutation, qualifier deletion, number word "two", relation word "exceeds"). The same six moves on this run's phrases (judge's variants, `t5/variantsZ/`): **5/6 rejected** — d02 time swap and d03 species swap by P3 (designed and committed in the reader brief 5dfc17e before Z ran: blind), d04 by P6, d05 and d06 by P5 (both written after reading Z: not blind). Earlier open cases now caught: X d01 (redshift times swapped) by P3, Y d02 ("minus" deleted from `curvK`) by P4. Judge output: `t5/judge_Z.out`. **Weakest unchecked step:** relation sentences inside a phrase outside any blind sign clause (Z d01: "the deceleration parameter is [minus] the order 2 coefficient"); and the reader route itself (a forged reading committed in its own commit passes, as for every blind route).

## Start
- 22:27Z. add_repo not exposed; pre-cloned checkout detached with a stale shallow local main; `git checkout -B main origin/main` = 5481cb7. LOCK held by run 2026-11-08T2028Z (heartbeat 22:20Z, alive) → auditor role for five minutes (README stub badab37); run 2028Z removed its LOCK in 816c21b; LOCK taken 476bf0a (22:32Z), heartbeats.
- Environment: repo reachable (push); local Lean: elan + toolchain v4.35.0 + Mathlib cache ≈ 2 min; full `lake build Checked` 22:32–23:49Z (77 min, MMCerts first 6 min, 2 cores); StatementDeps ≈ 5 min, Claims ≈ 3 min.
- CI read: ca0dfff (42523479762) green on all nine jobs (read by run 2028Z). Promotion 26d2718 (42529715818): work, packet, goal guard, nanoda shards 0 and 2 green, shards 1 and 3 still running at 22:55Z, **checked job cancelled by coalescing** → the β = 1/5 trio becomes PROVED with the first later main run whose checked job is green (this run's e16541a carries it).

## Bottleneck
STATE exact next step 2 (part 3, rotation after 2028Z's parts 2/5): rounds X and Y left one class of the phrase layer open — words quoted from a definition's own spec but put in the wrong place (roles swapped, a "minus" dropped). A yes binds every argument's role and every sign convention to an independent blind reading; a no leaves CLAIMS.md (what the program tells scientists to rely on) with author-placed role words next to correct Lean bodies that name arguments only by symbols.

## Work
1. Brief of a blind role reader committed alone (5dfc17e); red team Z's brief committed alone (0234518); reader and red team (both Sonnet) launched in ONE message, the red team on a read-only snapshot worktree of 5dfc17e. The planned rules P3 (role binding) and P4 (sign conventions) are stated in the reader brief's purpose, i.e. fixed before Z ran.
2. Reading f9f190c: 95 ROLE lines (one per binder of the 23 pinned definitions) and 13 SIGN conventions, from the specifications, pin theorems and Lean bodies only. Red team Z output committed 7754ecc before judging.
3. `scripts/trust/check_claims.py`: **P3** each placeholder's first occurrence is immediately preceded by its blind role, and every placeholder has one; **P4** each blind SIGN convention occurs word for word; registry lines must occur verbatim in a reader file under `runs/` next to its BRIEF.md; `--base` checks brief → reading → copy in three commits (reading commit touching only its run folder). Controls added to `_controls()`.
4. After reading Z (not blind): **P5** number/sign/comparison words are no longer function words for P2 (13 grandfathered pairs in the new shrink-only `scripts/trust/phrase_polar_baseline.txt`); **P6** a second blind reader (brief 08de55a alone, reading 07b922a) named each pinned definition with its qualifiers; the name must occur word for word.
5. All 23 phrases reworded by script (`scripts/new_phrases.py`, `name_phrases.py`, `vocab_phrases.py`); CLAIMS.md, FINDINGS blocks and the validation packet regenerated; 37 claim-vocabulary baseline lines that no longer fire removed (shrink). Commit e16541a (LEDGER line names every changed phrase).
6. Scratch for STATE next step 4 (`lean/UpperBound.lean`, compiled against the built Checked tree, axioms propext/choice/Quot.sound): `le_one_of_tendsto` — at an interior maximum of p = f' above one, f'' = 0 and the equation gives f''' = f'² − 1 > 0, so there is none; hence every solution of the stagnation-point equations with f'(0) = 0, f' → 1 has f' ≤ 1, and `hiemenz_lower_window`, `homann_lower_window` restate the window theorems with only −1 ≤ f'. The lower bound is the open part (referee_bounded.md §3).

## Judge (`t5/scripts/judge_Z.py`, phrase-only: `.lake/phrases.jsonl` of this run's build for both trees)
| defect | move | snapshot 5dfc17e rules | this run's rules (same move on the new phrases) |
|---|---|---|---|
| d01 | "minus" deleted in cosmoCoeff's relation sentence | passes | **passes** (open) |
| d02 | lumDist times swapped | passes | rejected, P3 (blind) |
| d03 | MM species permuted | passes | rejected, P3 (blind) |
| d04 | "flat" deleted (IsFlatLCDM) | passes | rejected, P6 (not blind) |
| d05 | "κ is two" (rhoM) | passes | rejected, P5 (not blind) |
| d06 | "equals" → "exceeds" (Maxwell) | passes | rejected, P5 (not blind) |

## Commits
badab37 stub · 476bf0a LOCK · 5dfc17e reader brief · 0234518 brief Z · f9f190c reading · 7754ecc red team Z output · 08de55a name brief · 07b922a name reading · heartbeats · e16541a rules, registry, phrases, regenerated files · records (this commit, LOCK removed).

## CI
- e16541a and the records commit: read next run (the first main run whose checked job finishes also judges the β = 1/5 promotion 26d2718).
