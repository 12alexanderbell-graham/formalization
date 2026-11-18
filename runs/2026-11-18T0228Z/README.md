# Run 2026-11-18T0228Z (scheduled)

**THE RESULT:** part 3 by rotation (STATE 1h → 1f (iii)) — the three-reader test applied to the other labelled pages a scientist meets. CLAIMS.md now carries a **generated Status line under every headline** (its `Checked` module and the axioms `Lean.collectAxioms` returns — 294/294 standard; any other axiom is a blocking generator error — and the rule that a headline is withdrawn only by leaving `Checked` and the registry). STATE.md's and README.md's banners name that line as the status of record (goal guard). Measured with 17 blind readers, pre-registered (`t5/reader_brief.md`, `t5/READERS.md`).

**What can a scientist now trust without checking it themselves, that they could not before?** That every headline on CLAIMS.md is proved in `Checked` using only `propext`, `Classical.choice` and `Quot.sound`, read off the page itself (computed by Lean when the page is generated; CI fails if the page is stale) — before, the page said nothing about status, and a hand-written "withdrawn" next to it made 6/6 readers answer "no". With the line, 0/6 answer "no"; 6/6 still answer "unclear". Measure: blind readers misled into "no" 6/6 → 0/6; into "unclear" 0/6 → 6/6 (criterion "at most one of three misled" not met on either page); a contradicted overstatement in a paraphrase misleads 0/3 before and 0/3 after, and no longer costs a valid result its "yes" (2/3 "unclear" → 0/3).

**Weakest unchecked step:** hand-written status sentences in STATE.md (and run records) about registered headlines: a withdrawal line passes every check and still makes careful readers withhold citation, because its stated reason (a fidelity flaw) is a claim about meaning that no generated line answers. A word rule against it (S3) was built, attacked (≈ 40 bypasses in six classes, false positives on correct lines) and not shipped (`t5/S3_ADVERSARY.md`).

## Start
- 02:28Z. add_repo not exposed; checkout on main at fa47717 = origin/main. No LOCK → taken (a0ebddd).
- Local Lean: elan installer + `lake exe cache get`; `checked-build` of 43755149508 (5c6a05b) restored with DELETE_ZIP=1 (4 GB free afterwards); `lake build Checked` replayed + `NecessityAQ` (< 2 min); Claims ≈ 4 min; StatementDeps (no relock) ≈ 12 min.
- CI at start: 44217681379 (fa47717, `NecessityAQ`) in progress (nanoda shards and the checked job running; goal guard, packet, work green). Not read to the end: this run's final push supersedes it; the next run reads this run's CI, which judges `NecessityAQ` too (diff base = newest green ancestor 5c6a05b).

## Bottleneck (and what a yes/no changes)
- Rotation: part 3. Run 2026-11-15T1628Z showed on the findings page that a labelled hand-written line that nothing generated contradicts (a withdrawal) misleads 3/3 readers while a contradicted one misleads 0/3. Question: does the same hold on CLAIMS.md (author paraphrases under a label) and STATE.md (banner)? Yes → those labels do not protect, and the generated pages they point to must speak about what the prose can claim. `TRUST_MAP.md` has no author-controlled sentence, so no arm.

## What we did
1. Pre-registered (a0ebddd) five arms, prompt, key and decision rule; pages by `scripts/make_reader_pages.py`: W (withdrawal in the paraphrase of `gelfand_pde_radial_many_centre`), G (β-range overstatement in the paraphrase of `fs_neg_reversed_wall_shear_3_exists`), W′ (withdrawal bullet in STATE.md), a CLAIMS page without paraphrases.
2. Before (r1–r11): W misled 3/3 (clean 0/2), W′ 3/3 (control 0/1), G 0/3 on scope but 2/3 turned (a) to "unclear"; the paraphrase-free page answered as well as the clean page (one deviation each on parameter-free items, the same deviation the clean readers made) but failed the literal usability rule, so by the rule the paraphrases stay.
3. Fix by rule 4: the generated Status line (`scripts/trust/Claims.lean`, CLAIMS.md regenerated, 294 lines) and a fixed preamble paragraph; banners in STATE.md and README.md (goal guard requires the sentence); the validation packet regenerated (its items quote CLAIMS sections).
4. Hardening found while wiring it: `check_claim_vocab.py` reads every non-paraphrase line of a section as claim vocabulary, so the Status line's fixed words (withdrawn, registry, prose) would have become words a paraphrase may use (a weakening of V1). Both parsers that read sections (`check_claim_vocab.sections`, `check_numbers.claim_sections`) skip the line; control G1 in `controls/prose_rule_controls.py` (planted paraphrase "withdrawn by the registry" through the real parser) fails if they stop doing so (verified by reverting the skip: G1 fails).
5. After (r12–r17, arm pre-registered 3a83ff0): "no" 6/6 → 0/6, "unclear" 6/6; readers quote the Status line against W/W′ and withhold citation on the fidelity reason ("does not say what the source says"); two thought the generated page might lag.
6. CI acceptance of the defects (current checks, files swapped in place): W and G are rejected by `check_claim_vocab.py` V1 (their words are not the claim's own); W′ passes `check_status_lines.py` and `precheck_citations.py`. S3 built and attacked, not shipped (`t5/S3_ADVERSARY.md`, patch kept).
7. Local: `lake build Checked`, Claims, StatementDeps (TRUST_MAP unchanged), `records_check.py 5c6a05b`.

## Next
- STATE 1i.
