# Run 2026-11-09T0228Z (scheduled)

**THE RESULT:** part 3 — the plain-words phrase of every pinned definition, the only hand-written text in a generated claim, is now **generated from blind readings alone**: every word, number, Greek letter and mark of it lies inside a text written by a blind reader of the definition's specification (its name, the role of each argument, its sign conventions, and every clause a third reader wrote), joined only by "the a an and with" and punctuation; CI (rules P7–P9) enforces it, and the author can no longer choose which blind clauses to show except through a shrink-only list with reasons. Measured by blind red team AA (6 defects) and adversary AB (5 defects) in the same run.

**What can a scientist now trust without checking it themselves, that they could not before?** That no sentence of a generated claim's definition phrase was written by the author who proved the theorem: relation sentences ("the order 2 coefficient is minus the deceleration parameter"), unit conventions, reaction mechanisms with their rate constants, intervals and domains come word for word from blind readers of the specifications, and none of them can be dropped, reordered inside, re-bracketed or tied to another argument without CI failing.

**Measure (phrase layer):** blind red team AA (Sonnet, brief f02c700 committed alone; P7 designed and stated in the clause reader's brief dd48d82 before AA ran): as submitted against the snapshot's rules **6/6 pass**; the same six moves on this run's phrases (judge's variants `t5/variantsAA/`): **6/6 rejected, each by P7 (coverage), designed before AA ran: blind**; d03 and d04 (registry lines deleted) are also rejected by P8 (written after reading AA), and d04b (a SIGN line deleted with its text, no false sentence) by P8/P9 only. Adversary AB (Sonnet, on P7/P8 as first implemented, fe8d722): **4/5 pass** as submitted (d01 caught by the existing U2); the same five moves after the repair: **0/5 pass** (not blind). Round Z d01 (the open case of run 2228Z, "minus" deleted from a relation sentence): rejected (P9 required clause, P7).
**Weakest unchecked step:** the reader route itself (a forged brief + reading committed in their own commits passes, as for every blind route), and the author's remaining choices: which binders are the subject of a predicate, its verb, and the 27 exclusions of `phrase_clause_baseline.txt` (shrink-only, each with a reason; an exclusion hides information but cannot add a false sentence).

## Start
- 02:28Z. add_repo not exposed; pre-cloned checkout detached with a stale diverged local main; `git checkout -B main origin/main` (local branch only) = 4a00073. No LOCK; taken in 1201ad2.
- Environment: repo reachable (push); local Lean: elan + toolchain v4.35.0 + Mathlib cache ≈ 3 min; full `lake build Checked` from 02:35Z (see below); Claims.lean after it.
- CI read: 3684e58 (42549988367, the no-bound Falkner–Skan promotion): goal guard, packet, changes, **work job green** (judges `Work/FalknerSkan/UnrestrictedCore.lean`, `Unrestricted.lean`, `UBlindClosed.lean`), nanoda shards 0–2 green, shard 3 running at 02:48Z, **checked job cancelled by coalescing** (by 4a00073's run 42550201653, pending at 02:30Z) ; then **4ca5437 (42552130020, this run's push of red team AA's output, a descendant of 3684e58) green on every job incl. the checked job → the eight `*_limit_*` headlines are PROVED**.

## Bottleneck
STATE exact next step 3 (part 3; rotation after 0028Z's parts 2/5): relation sentences in phrases, open since round Z d01 — 21 of 23 phrases carried author-written words outside every blind text (prototype count, `scripts/coverage_proto.py`). A yes makes the generated claims' definition phrases entirely blind text; a no leaves the one hand-written layer of CLAIMS.md (what the program tells scientists to rely on) open to an unnoticed false relation, unit, mechanism or domain.

## Work
1. Clause reader brief dd48d82 (purpose: rule P7 stated before any red team), red team AA brief f02c700, both committed alone; reader and red team (Sonnet) launched in ONE message, AA on a read-only snapshot of f02c700. Reading 23af037 (104 CLAUSE lines), AA output 4ca5437, both committed before any rule was written or judged.
2. Letter reader (cosmographic q, j, s, l; brief 0eb1c4b alone, reading committed alone): needed because `check_numbers.py` R4 ties FINDINGS symbols to the cosmoCoeff phrase. It did not name order 6 (m): m₀ → order 6 now rests on the SYMBOLS table of `check_numbers.py` alone (known gap).
3. Every clause used was checked against the definition's Lean body by the main session (all true; ambiguous parses excluded).
4. P7 (coverage) + P8 (registry cannot lose a line) implemented with controls (8906b8e); adversary AB on that commit (fe8d722) found five holes; repaired (dd087fc): neutral connectives, marks as tokens, verb touches the NAME, P9 (every registry clause required; shrink-only exclusion baseline with reasons; excluded lines cannot be in the registry). Phrases generated from the registry (`scripts/gen_phrases.py`).
5. Claims.lean (218 claims), check_claims (23 phrases, 0 problems), check_claim_vocab: 3 reader clauses excluded for glossary attribution (U2), 7 neutral nouns added to `prose_vocab.txt` (paraphrases had borrowed them from the old author phrases: model, sign, field, expansion, fraction, mechanism, network), 35 claim-vocabulary baseline lines that no longer fire removed (shrink). Validation packet regenerated.

## Judge (`t5/judge_AA.py`, phrase-only: `.lake/phrases.jsonl` of this run's build for every tree; full output `t5/judge_AA.out`)
| defect | move | snapshot rules | this run's rules (same move on the generated phrases) |
|---|---|---|---|
| AA d01 | Ω_k → Ωₘ in "… is one minus Ω₀" (omega0) | passes | rejected, P7 (blind) |
| AA d02 | rate constants k₂/k₃ swapped between reactions (Robertson) | passes | rejected, P7/P9 (blind) |
| AA d03 | NAME line deleted, "with dust" dropped (FriedmannEq) | passes | rejected, P7 (blind), P8 |
| AA d04 | SIGN line deleted, "minus" → "is" (curvK) | passes | rejected, P7 (blind), P8 |
| AA d05 | liquid/gas volumes permuted after first placeholder (Maxwell) | passes | rejected, P7/P9 (blind) |
| AA d06 | closed → open interval brackets (Duffing) | passes | rejected, P7/P9 (blind) |
| AA d04b | SIGN line and its text deleted, nothing false added (judge's) | — | rejected, P8/P9 |
| AB d01 | "at"/"for" swapped between role texts (rhoM) | rejected, U2 | rejected, P7 connectives |
| AB d02 | "from … to" reversing the integral (comoving) | passes | rejected, P7 connectives + P9 |
| AB d03 | optional clause "divided by the n-th power of the Hubble rate" omitted | passes | rejected, P9 |
| AB d04 | parentheses regrouping a blind clause | passes | rejected, P7 marks |
| AB d05 | rejected reader line copied into the registry later | passes | rejected, P9 (required clause) and baseline-in-registry rule |
| Z d01 | "minus" deleted in cosmoCoeff's relation sentence (open since run 2228Z) | passes (Z snapshot) | rejected, P7/P9 |

## Commits
1201ad2 LOCK + stub · dd48d82 clause brief (P7 stated) · f02c700 brief AA · 23af037 clause reading · 4ca5437 AA output · 0eb1c4b letter brief · letter reading · 8906b8e P7/P8, registry, phrases · fe8d722 brief AB · AB output · dd087fc P7 repair + P9, generated phrases · 94b8c65 heartbeat (second worktree) + merge · CLAIMS/packet/vocabulary · records (LOCK removed).

## CI
- 4ca5437 (42552130020): green on every job (checked: build 32 min, trust step 9 min, frozen registry, author files; nanoda memoised) → `*_limit_*` headlines PROVED.
- a98a677 (42560045819, phrases + CLAIMS.md): pending at 04:09Z — read next run.
