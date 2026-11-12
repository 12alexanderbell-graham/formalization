# Run 2026-11-12T1028Z (scheduled)

**THE RESULT:** parts 2/5 by rotation — the three Falkner–Skan candidates whose Lean evidence is PROVED (C-FS-SEP, C-FS-1988, C-FS-1988R; STATE next step 0a, deferred by three runs) are verified findings F12, F13, F14 with certified records.

**What a scientist can now trust without checking:** that the separation parameter printed by Fazio (2012, 2020), five tabulated attached-flow wall shears at β = −0.1988 (Fazio 2012; Asaithambi 2005, Zhang–Chen 2009, Salama 2004 as tabulated by Asaithambi 2021; Zhu–Cheng–Wu) and Fazio's reverse-flow wall shear are wrong, with the gap between each of Fazio's three printed values and the true value of every solution shown as a Lean rounding, generated next to the Lean statement in FINDINGS.md (`Checked.Records.F12_separation`, `F13_wall_shear`, `F14_reversed_wall_shear`).

**Weakest unchecked step:** the printed values themselves for Asaithambi 2021 and Zhu–Cheng–Wu were read through a summarizer only (typeset reading open); later arXiv versions or errata of the Fazio papers were not read; hypotheses 4–9 of F12 and 1–8 of F13 are open (as in the headlines they restate).

## Start
- 10:28Z. add_repo not exposed; pre-cloned checkout detached; `git fetch --unshallow` + `git checkout -B main origin/main` = 0e262e6; no LOCK (taken 052b0cb, 10:40Z).
- Local Lean: elan installer accepted, Mathlib cache ≈ 3 min; CI artifact `checked-build` (run 43155541876, 7ddd986) restored in 75 s (needed `pip install zstandard`: no zstd binary); `lake build Checked` on top 7 min.
- CI: run 43196172253 of 0e262e6 (Bonnor–Ebert promotion + AH repair): work, goal guard, packet, nanoda 0 and 2 green; its checked job pending.

## Bottleneck
- STATE 0a: C-FS-SEP, C-FS-1988, C-FS-1988R had PROVED Lean evidence since run 0227Z's CI read (37b67ea green on every job) but stayed candidates: their decimals stood in author prose with no certified record. Yes → three published-value refutations become verified findings a reader can check number by number; no → the record pipeline cannot carry quantified ODE solutions.

## Work
- `Checked/Records/FalknerSkan.lean`: three records, each a corollary of PROVED headlines with the hypotheses copied verbatim — `F12_separation` (printed − β, 8 decimals), `F13_wall_shear` (printed − q(0), 6 decimals), `F14_reversed_wall_shear` (a reverse-flow solution, q(0) − printed, 7 decimals) — against three PRINTED definitions (`printedFazioSeparation` with the existing reading; `printedFazioWall`, `printedFazioRevWall` with a new blind reading from the typeset crop, `fsval_reader2/`, brief 9b97dec, reading 1fdfa88; the first reader `fsval_reader/` gave the same values but had the crop in its folder, which B5 of `check_blind_route.py` rejects). The first version certified the true values as free roundings; `check_prose.py` rejected it (`free-record`: a record must reach a pinned or transcribed definition) — there is no pinned Falkner–Skan solution predicate, so true values of FS quantities cannot yet be records on their own.
- NV witnesses (Witnesses.lean), necessity 1–3 of F12 (`Checked/Trust/NecessityN.lean`, NecessityE's profiles at the printed β), literal readings, open baseline, relock, TRUST_MAP (244 headlines, NV 161/161, NEEDED 425), CLAIMS, FINDINGS blocks (`check_numbers.py --write`: 29 certified values), packet.
- FINDINGS F12–F14 written from the candidate entries; certified values only in generated blocks; printed `[src]`, referee `[unc]`.
- Local CI replica on the final tree: the checked job's trust step (StatementDeps with relock and Claims freshly regenerated, then every Python trust check) exit 0, and `local_frozen_step.py cc6673d` (base-diff step) 20/20 green; goal guard and precheck_citations green. Three rounds were needed: check_prose `free-record` (true values without a pinned predicate → printed − true differences against PRINTED definitions), check_claim_vocab V1/V12/V14 (docstrings now quote the generated claim), check_blind_route B5 (crop beside the brief → second reader) and the LEDGER disclosure of the two readings by bare name. The role classifier labelled `printed − β` a "printed value": fixed (difference with a free side).

## CI incident and repair
- Main run 43175455329 (f789e4d) had its checked job in the build step from 07:32Z (green checked jobs: 35–100 min); through the per-ref job concurrency it held 0e262e6's checked job pending. Cancelled at ≈ 11:00Z (f789e4d is an ancestor of 0e262e6). Its cancelled job went on running the `always()` author-files steps.
- Repair (lean.yml, LEDGER, 39.5): `timeout-minutes: 240` on the checked job; the four post-check `always()` steps → `!cancelled()`.

## Not done
- C-BE-1 (Galli et al. 2002's 13.98): needs a reading of the paper's other numbers; arxiv.org WebFetch permission was not answered this run, so no reading (no other route).

## Next run's starting point
- Read CI by run ID: main run 43196172253 of 0e262e6 (Bonnor–Ebert promotion + AH repair; checked job started 11:05Z after the cancel) and the run of this run's merge to main (records F12–F14, lean.yml repair). Green on every job → `bonnor_ebert_critical` and the three records PROVED; send Alexander one L.2 message if this run's notification did not already cover it.
- Then STATE next step 0 (part 1 by rotation).
