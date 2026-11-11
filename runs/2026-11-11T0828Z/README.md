# Run 2026-11-11T0828Z (scheduled)

**THE RESULT:** parts 2/5 (new science through the system): the Falkner–Skan limiting value β_min = −0.1988376 printed by Fazio (2012, 2020) is refuted in Lean as a corollary of the certified separation window (`Checked/FalknerSkan/SeparationPrinted.lean`, on branch `wip/sep-printed-promo`, CI pending — not yet merged, not yet PROVED); the stronger case behind it — five published wall-shear values at β = −0.1988 all wrong in the 4th digit — is filed (C-FS-1988) and its Lean statements are frozen (`Work/FalknerSkan/Neg1988.lean`).

## Front page (plain words)
- **What happened:** two papers print −0.1988376 as the pressure-gradient value at which the boundary layer separates (zero wall shear). The program had already proved the true value lies in (−0.1988377351, −0.1988377350). This run read the printed value from the typeset pages, had a blind reader transcribe it, stated "every separation profile's β differs from the printed value" in Lean, had a blind restater write the claim from words, and closed that restatement from the theorem.
- **Why it matters:** a published numeric claim is refuted by a machine-checked proof whose inputs (the printed number, the equation) were each read twice, blind. The same referee report held a stronger, unfiled case (tables at β = −0.1988 wrong in the 4th digit, five sources); it is now the next target, frozen.
- **What is not done:** the promotion's CI checked job had not finished when the run ended (CI builds took > 90 min today; no local Lean); the h2 necessity witness and the blind closure are written but not yet compiled; β = −0.1988 is frozen, not proved.
- **Can a scientist trust more without checking?** Slightly, once merged: one more printed value refuted by a checked proof; and a planned refutation of five published values.


## Start
- 08:28Z. Repo pre-cloned (detached HEAD); `git fetch --unshallow` + `git checkout -B main origin/main` = d4b1e37.
- LOCK held by run 0628Z (heartbeat 08:23Z, final relock running) → auditor role (rule 48.4): writes only in this folder and a CHANGELOG append.
- Local Lean: the elan installer was refused by the environment → not worked around (PROMPT instruction 4); CI judge only.

- LOCK released by run 0628Z (7f5e9c6); LOCK taken 08:40Z.

## Plan (bottleneck and what a yes/no changes)
- C-FS-SEP rests on WebFetch summaries of the printed values. Typeset read (arxiv PDF → page → crop → blind reader) of both Fazio papers. Yes (printed values as summarised): the candidate's printed side is confirmed and can go to FINDINGS proper once the Lean evidence is promoted (it is: `fs_separation_exists`/`fs_separation_equal` in Checked). No: correct the candidate or drop it.

## Typeset reading (C-FS-SEP), 08:30–08:50Z
- Both papers exist only as v1 on arXiv (v2–v4: 404). Crops in `typeset/`: Fazio 2012 p. 5 eq. (1.5) (same equation f''' + f f'' + β(1 − f'²) = 0 as ours), p. 6 eq. (1.6) "β_min = −0.1988 …", p. 16 (β = −0.198837723795, skin friction ±6.61D−06, truncated boundary 1), p. 28 Fig. 4 caption; Fazio 2020 p. 22 Fig. 7 caption. Both captions: "β = −0.1988376. We notice that d²f/dη²(0) = 0".
- Blind reader (Sonnet, brief 309689c committed alone first): `sep_printed_reader/SecondReadingFSSepPrinted.lean`, `fsSepPrintedFazio := -(1988376 / 10000000)`; both captions agree; equation form matches. (The reader left "v?" for the arXiv versions; both are v1.)
- Nuance (already in the 0232Z referee report): for β* < β < 0 a zero-wall-shear solution with an algebraic tail exists, so the caption's claim is false only in the classical (exponential-decay) class, the class in which Fazio's text says the limiting solution is unique.
- Planned Lean (after the LOCK is released): `fs_separation_printed_not` — no zero-wall-shear decay-class solution at β = −0.1988376, from `fs_separation_exists` + `fs_separation_equal` (the printed value lies outside the certified window).

## Lean (after the LOCK release, 08:41Z)
- Headline `Checked.FalknerSkan.SeparationPrinted.fs_separation_below_printed`: for every zero-wall-shear solution of f''' + f f'' + β(1 − f'²) = 0 in the decay class (q > 0 beyond the wall, for every M eventually M(1 − p) ≤ q), β ≠ −1988376/10⁷. Proof: `fs_separation_equal` with the witness of `fs_separation_exists` puts β in the certified window (−0.1988377351, −0.1988377350), which excludes the printed value (by 1.35·10⁻⁷).
- Literal reading `fsSepPrintedFazio` (blind, above); NV witness (the separation solution); necessity (`Checked/Trust/NecessityE.lean`): hypotheses 1 and 3 NEEDED by the profile p = 1 − e^{−kη²}, k = 1988376/20000000 (q'(0) = 2k = −β, so the equation holds at the wall with the junk value f(0) = 0); 2, 4–9 disclosed open.
- Fidelity audit: blind restatement (Sonnet, claim in words; brief b9603c0 committed alone) `blind/SepPrintedBlind.lean` (separate functions f, f1, f2, f3, β as the decimal −0.1988376, `¬ ∃`), closed in Lean from the headline (`Work/FalknerSkan/SepPrintedBlindClosed.lean`). Not vacuous (NV), not trivial (needs the certified window: a printed value inside the window could not be excluded), junk values: none (≠ on ℝ, no division). Referee: run 0232Z's independent β* = −0.19883773504667754688… (35 digits) is 1.35·10⁻⁷ below the printed value.
- No local Lean: compile tests on `wip/sep-printed` (work job), promotion on `wip/sep-printed-promo` (checked job → author files).

## Also this run
- Frozen `Work/FalknerSkan/Neg1988.lean` (50de3b1): `fs_neg1988_window`, `fs_neg1988_exists_decay`. Independent numerics: scipy DOP853 bisection on the overshoot boundary, f''(0) = 0.005218187884 (horizons 12, 14), agreeing with run 0232Z's referee (0.00521818788391).
- Reader (Sonnet, brief ca0c56d committed alone): Asaithambi, Fluids 6 (2021) 153, Table 2, β = −0.1988: 0.005225, 0.005222 (Zhang et al.), 0.005226 (Salama); HTML via summarizer only — the MDPI PDF returned 403 and was recorded "not read" (not worked around).
- h2 necessity witness (`lean/NecessityPrintedH2.lean`: p = min(η, 1), q solving the linear q-equation at the printed β) and the blind closure: pushed to `wip/sep-printed` (562e4a9), not yet compiled (that run was cancelled to free CI runners).
- CI housekeeping: cancelled the superseded branch runs 42975694116, 42978251321 (`wip/necessity-d*`, already merged by 0628Z) and 42988291350 (own compile test): seven Lean runs were building at once, each > 90 min.
- PROMPT working note: referee side observations are FINDINGS candidates the same run.

## β = −0.1988: certificates found (Python, exact rationals)
- `scripts/gen_neg_wc_theta.py` (copy of run 2026-11-09T0828Z's `gen_neg_wc.py` with the slow threshold θ and a fine start step as options) and `scripts/make_neg1988.sh`: at K = 2500/497, **Slow at A = 0.011703189 (134 cells) and Over at A = 0.0117034 (142 cells) both close** — the two chain certificates of the window (0.0052181, 0.0052182) exist. The first try failed only because the first cell's crude q-range (q(0) = 0.0117, step 1/32) dipped below 0: a step 1/128 on [0, 1/16) fixes it. Remaining work is the Lean side (template `Checked/FSNeg/` to K = 2500/497, θ = 11/15).

## CI of the promotion
- 42989694522 (8d0ce16): checked job build 78 min; **every new module built (the headline, the reading, the NV witness in Witnesses)** except `Checked/Trust/NecessityE.lean` (3 errors: derivative of `exp(−k η²)` in the Pi-negation form, a product derivative in Pi form, the h1 witness tuple started with the wrong derivative). Fixed blind in 0c2fe8b (no local Lean), with h2 and the blind closure added as Work files; superseded runs cancelled (42989694522 after its checked job, 42990806831).

## CI rounds 2–3 of the promotion, and hand-off (13:05Z)
- 43001835490 (0c2fe8b): Checked build green (NecessityE fixed), nanoda 4/4 shards green on the new modules, work job green incl. the h2 witness and the blind closure; trust step red only on relock. Python suite on its author files: check_prose (decimals and arXiv ids in two module docs), check_literals (`source=Fazio` applied to another reader's constants), check_literal_targets T1/T2 (a printed value on a `≠` side is no certified target), check_claim_vocab (baseline lines silenced by `printed`).
- Repairs (318e711, 0e7839e): conclusion `β < -(1988376 / 10000000)` (stronger, and the printed value is now a certified target side), name `fs_separation_below_printed`, reader line split, slot `target` for `fsSepPrintedFazio`, module docs without decimals, h2 moved into `Checked/Trust/NecessityE.lean` (open 4–9).
- 43016082467 (0e7839e): build green; with its author files every Python check of the trust step is green except check_claim_words W1 ("so" in the headline docstring) and check_claim_vocab (`fazio`, more silenced baseline lines) → fixed in 17f5b2d–efdb2d6 (docstring reworded, `fazio` disclosed vocabulary, 18 silenced baseline lines removed). The reworded docstring needs one more relock (its doc hash) and a CLAIMS regeneration: CI 43025384759 on efdb2d6 produces them, or a run with local Lean does it in minutes.
- Hand-off: LOCK released at the end of this run; run 2026-11-11T1228Z (local Lean) or the next holder merges (STATE exact next step 1).

## FINDINGS draft (apply when the promotion is merged; cites the new headline by name)
### C-FS-SEP (runs 2026-11-11T0232Z, 0828Z; Lean evidence in Checked, PROVED once its main run is green): the Falkner–Skan limiting value printed by Fazio (2012, 2020) is wrong in the 7th digit
- **Printed (typeset read, run 0828Z, crops in `runs/2026-11-11T0828Z/typeset/`; blind literal reading `Checked.Trust.SecondReading.fsSepPrintedFazio`):** Fazio, arXiv:1212.5057v1 (2012), Fig. 4 caption (p. 28) and arXiv:2011.07725v1 (2020), Fig. 7 caption (p. 22): "Numerical solutions to Falkner-Skan model for β = −0.1988376. We notice that d²f/dη²(0) = 0", the text calling it the unique solution at the limiting value β_min; same equation f''' + f f'' + β(1 − f'²) = 0 (2012 eq. (1.5)). The 2012 text (p. 16) also reports, at β = −0.198837723795 (IVP solved on [0, 1]), skin-friction coefficients ±6.61·10⁻⁶.
- **Lean evidence (Checked, run 0828Z):** `Checked.FalknerSkan.SeparationPrinted.fs_separation_below_printed` — the β of every zero-wall-shear solution with f'' > 0 beyond the wall and faster-than-every-exponential approach lies below −0.1988376 (from `fs_separation_exists`, `fs_separation_equal`: such β lie in (−0.1988377351, −0.1988377350)).
- **Second route:** run 0232Z referee (`runs/2026-11-11T0232Z/referee/REPORT.md`): β* = −0.198837735046677546889…; at β = −0.198837723795 the wall shears are ±8.96·10⁻⁵, not ±6.61·10⁻⁶.
- **Scope:** for β* < β < 0 a zero-wall-shear solution with an algebraic tail exists, so the caption is false only in the classical class (exponential approach), the class in which the paper calls the solution unique. Changes no qualitative conclusion of the papers.
- **Remaining:** PROVED needs its main CI run green on every job.

### C-FS-1988 (run 2026-11-11T0828Z, from the run 0232Z referee's side observation; statements FROZEN in `Work/FalknerSkan/Neg1988.lean`, unproved): every printed value found of the attached Falkner–Skan wall shear at β = −0.1988 is wrong in the 4th significant digit
- **Printed:** Fazio 2012 (arXiv:1212.5057v1, p. 16, typeset read run 0828Z): 0.005221 (and −0.005158 for the reversed-flow branch); Asaithambi, Fluids 6 (2021) 153, Table 2, row β = −0.1988 (run 0828Z reader, `runs/2026-11-11T0828Z/fs1988_reader/READING.md`; HTML through a summarizer only, the MDPI PDF returned 403 and was not read): 0.005225 (Asaithambi), 0.005222 (Zhang et al.), 0.005226 (Salama); per the 0232Z referee also Zhu 0.005229 (not read).
- **Numerics (two routes, uncertified):** run 0232Z referee (mpmath, ≈ 12 digits shown) 0.00521818788391; run 0828Z scipy DOP853 rtol 10⁻¹³ bisection on the overshoot boundary, horizons 12 and 14: 0.005218187884. Lower branch −0.00515742017793 (Fazio −0.005158 is wrong in the last printed digit).
- **Planned Lean:** `fs_neg1988_window` (every decay-class solution with q > 0 on [0, ∞) has 0.0052181 < q(0) < 0.0052182) and `fs_neg1988_exists_decay`; route in STATE "Exact next step".

