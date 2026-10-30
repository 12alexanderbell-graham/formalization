# LEDGER (append-only)

Claims and status changes, failed approaches with root causes, corrections, integrity events. Never edit an earlier entry; append a correction that references it.

## 2026-10-30 · integrity event · CI judge defined
- `.github/workflows/lean.yml` created: job `work` builds the `Work` library (sorry allowed); job `checked` builds `Checked` with axiom-audit (allowlist propext, Classical.choice, Quot.sound), leanchecker and nanoda (sorry not allowed).
- Status: UNTESTED. Must pass positive controls (annex 39.6) before any result is called PROVED.

## 2026-10-30 · governance · annex v3.0 → v3.1
- Added 40.0 (full fidelity audit applies to headline statements and definitions, not helper lemmas), a results-first preference in 42.1, "Physlib formatting only when preparing a contribution" in 47.1, and LIII (pace and accountability: 2-run target pick, 3-run first milestone, daily review, 24-run stall rule, short records).
- Reason: Alexander asked for a review aimed at results, not strategy. These cut audit and formatting overhead and add deadlines that turn 12 runs a day into results.
- Added CONSTITUTION_COMPLETE.md (all parts in one file) and governance/SHA256SUMS.

## 2026-10-30 · integrity event · lake-manifest.json added
- First CI run (40965992094) failed before building: lean-action requires `lake-manifest.json`, and Lean could not be run locally to generate it.
- Fix: copied Physlib's manifest (same toolchain, Mathlib v4.35.0 at 56a005855ea17e0b0958f73ec801ae140b0a1679, which matches the v4.35.0 tag; all other packages are Mathlib's own pinned dependencies) and renamed the package. No check was changed.

## 2026-10-30 · integrity event · nanoda moved to own step
- CI run 40966121805: `work` green; `checked` built and passed leanchecker, then lean-action's built-in nanoda step failed because it could not detect a module name from our lakefile (it expects a `[package]` table and exports the package-named module). axiom-audit was skipped as a result.
- Fix (commit b4dbb86): nanoda disabled inside lean-action and run by `scripts/nanoda_checked.sh` on module `Checked`, same tools and settings as lean-action v1.7.0 (permitted axioms incl. Lean.trustCompiler, non-hard error). nanoda acts as the independent type checker; axiom-audit remains the axiom judge with the strict allowlist. No check weakened relative to the intended design.

## 2026-10-30 · integrity event · nanoda report-only (known gap)
- CI run 40966663174: lean-action step green, including leanchecker and axiom-audit ("audited 1 declaration(s) under 'Checked'; all within the allowlist"). nanoda failed with "invalid digit found in string" while parsing the 13.8M-line export: the current lean4export output format and nanoda_lib's `debug` branch don't match for Lean v4.35.0. This is a tooling incompatibility, not a problem with our proofs; lean-action's own nanoda step would hit it too.
- Change: nanoda step set to `continue-on-error` (report-only). Blocking checks are now: build, leanchecker (kernel replay), axiom-audit (strict allowlist), forbidden-token grep.
- Open: repair nanoda (e.g. pin a lean4export revision that matches nanoda_lib) and make it blocking again. Low priority versus results; do it when a run has spare capacity or before any result is reported as a finding.

## 2026-10-30 · S1 complete · the judge works
- main @ 6-commit head: CI run 40967111191 green (work + checked: build, leanchecker, axiom-audit).
- Positive control 1, branch `control/sorry-in-checked`: run 40967115479 FAILED as required; axiom-audit reported `Checked.control_false_claim → [sorryAx]`.
- Positive control 2, branch `control/axiom-in-checked`: run 40967118310 FAILED as required; axiom-audit reported `Checked.control_uses_axiom → [Checked.control_bad_axiom]`.
- Both caught by axiom-audit inside the lean-action step, before the grep backstop ran. Branches kept, not merged.
- Remaining judge gap: nanoda report-only (see entry above).

## 2026-10-30 · governance · annex v3.1 → v3.2 (LIV, ever-improving)
- Alexander's standing instruction: the program improves itself; when it notices a fundamental issue or a repeated pattern it studies and fixes it; he should never need to replace the scheduled task's prompt.
- Added annex LIV (duty to fix, daily pattern hunting, what runs may and may not change, every change logged as an experiment and evaluated later, stored prompt never needs replacing), a matching block in the operative core, and item 7 in PROMPT.md. Scheduled task prompt updated once, from the setup chat, to say the program maintains its own instructions.
- How to tell if it works: patterns logged in LEDGER get fixes within a run or two, and later runs record whether each fix helped.

## 2026-10-30 · run 2026-10-30T0028Z · S2 · target 1 picked
- Target 1: cosmographic low-redshift expansions (TARGETS.md #1). First milestone frozen at 6ef1003.

## 2026-10-30 · claims · two PROVED
- `Checked.Cosmography.lookback_second_order` STATED (6ef1003) → AUDITED (runs/2026-10-30T0028Z/audit.md) → PROVED (CI 40981530819, 40982411889; axiom-audit 12 decls within allowlist; leanchecker ok).
- `Checked.Cosmography.lookback_second_order_bigO` STATED (e5b5372) → AUDITED → PROVED (CI 40982411889).
- Blind restatement disagreement (o(z²) under C² vs O(z³) under C³), classified Underspecified; resolved by proving both; the blind statement verbatim is derived in Lean.

## 2026-10-30 · candidates · literature screen
- 9 cosmography papers, 105 printed formulas screened with sympy; 4 papers with candidate coefficient errors (FINDINGS.md C1–C4). UNVERIFIED: transcription through a summariser is the main alternative explanation. Not reported to Alexander as findings.

## 2026-10-30 · experiment (annex LIV) · local Lean via elan
- Problem: setup chat could not install Lean; every check would go through ~3-min CI round trips. Root cause: environment of that session refused the installer. This scheduled environment allowed it.
- Change: STATE.md records the exact install commands; runs use local Lean for iteration, CI as the judge.
- Expected effect: proof iteration in ~30 s instead of ~3 min. How to tell: next runs record whether the install works and how many CI pushes a milestone needs.

## 2026-10-30 · experiment (annex LIV) · minimal imports in Checked
- Problem: `import Mathlib` in a Checked file made the nanoda export step exceed 10 min (export of all of Mathlib). Root cause: nanoda/leanchecker work scales with the import closure.
- Change: Checked files import specific modules (Checked/Cosmography/Lookback.lean: 4 modules); Work files may import Mathlib. Recorded in PROMPT.md.
- Effect seen: CI run 40982411889 finished in 4 min (vs > 9 min for 40981530819). Keep.

## 2026-10-30 · run 2026-10-30T0220Z · first verified finding F1
- C1–C4: typeset text confirmed for all four (rendered PDF pages read as images; C2 also by pdftotext and the paper's own Table V). All four printed formulas are wrong as printed; crops in `runs/2026-10-30T0220Z/typeset/`.
- C2 → **F1**: Aviles et al. 2012 Eq. (15) l₀, m₀ misprinted; paper's numbers unaffected; misprint repeated in arXiv:1405.6935 Eq. (30).
- PROVED + AUDITED (Checked): `Checked.Cosmography.Aviles.flatLCDM_coeffs` (flat ΛCDM q₀…m₀, every Ω), `avilesL0Claim_false`, `avilesM0Claim_false` (Einstein–de Sitter), `Checked.Cosmography.AvilesWitness.printedL0_false_at` / `printedM0_false_at` (every Ω ∈ (0,1); m₀ except (√7−1)/3). CI 40996176398 green (first three); witness file: CI 40997256530 green with nanoda blocking. Blind restatement derived verbatim; referee STANDS-WITH-CORRECTIONS (corrections adopted).

## 2026-10-30 · integrity event · nanoda repaired, blocking again
- Root cause: `scripts/nanoda_checked.sh` used nanoda_lib's `debug` branch (2025-10), which predates lean4export's JSON format 3.1.0; and lean4export HEAD had moved to v4.36.0-rc1.
- Fix (27e6954): pin lean4export tag v4.35.0 (= our toolchain) and nanoda_lib master 8de7e0c. CI run 40996270496: "Checked 335889 declarations with no typechecker errors … nanoda: Checked passed" (one pretty-printer message, not a check failure).
- Then: `continue-on-error` removed; nanoda is a blocking check again (judge strengthened, no check weakened).

## 2026-10-30 · experiment (annex LIV) · typeset verification route
- Problem: run 0028Z's screen transcribed formulas through WebFetch's summariser, so every discrepancy had "transcription error" as its leading alternative; the arXiv LaTeX source is robots-blocked.
- Change: PROMPT working note: download arXiv PDF, render the page, read the image; check every version and the paper's own tables.
- How to tell: next screens go from candidate to typeset-confirmed or dismissed within the same run.

## 2026-10-30 · experiment (annex LIV) · generated proofs for derivative chains
- Problem: 5th/6th-order derivative identities are too long to write by hand in Lean.
- Change: sympy generator emits the `HasDerivAt` terms and `linear_combination` certificates (`runs/2026-10-30T0220Z/scripts/gen*.py`); the general flat ΛCDM theorem compiled in about 6 local iterations.
- How to tell: reuse for C4 (CPL) and later coefficients; count iterations per theorem.

## 2026-10-30 · governance note · Alexander: never ask for approval
- Recorded as PROMPT.md standing instruction 7. Runs do not ask him for permission; L.2 messages are information only. Environment refusals are not worked around (this run: local build of lean4export/nanoda refused → tested via CI).

## 2026-10-30 · run 2026-10-30T0430Z · second verified finding F2
- C4 → **F2**: Capozziello, Lazkoz, Salzano 2011 Eq. (22): CPL l₀ w_a² term missing a factor 9; paper's numbers unaffected (Fig. 2 follows the correct value); misprint reprinted in Bamba et al. 2012 (arXiv:1205.3421) Eq. (11.38).
- Frozen 4663ac9 → PROVED in Work (CI 41006086049 green) → AUDITED (`runs/2026-10-30T0430Z/audit.md`; blind restatement closed in Lean, CI 41007266062 green) → PROVED in Checked f6ce0b2 (CI 41007523313 green: build, leanchecker, axiom-audit, nanoda 336194 decls no errors): `Checked.Cosmography.CPL.flatCPL_coeffs`, `printedL0_ne`, `clsL0Claim_false`.
- `Checked.Cosmography.CPLExistence.exists_flatCPL`, `printedL0_false_at` (+ tool `exists_local_model`): AUDITED (addendum) → PROVED in Checked b6267ff (CI 41007796446 green, nanoda 374957 decls).
- Referee: STANDS-WITH-CORRECTIONS (corrections adopted; caveat "no interior-Ω model" closed by `printedL0_false_at`).

## 2026-10-30 · experiment (annex LIV) · ODE existence instead of closed-form witnesses
- Problem: refutations need a model with the printed formula's parameters; closed forms exist only for special parameters (F1 needed a sinh trick; C4's closed form only at Ω = 0). Root cause: witnesses were hunted case by case.
- Change: generic `exists_local_model` (Mathlib Picard–Lindelöf + C⁵ bootstrap) in Checked; PROMPT working note.
- How to tell: next refutations (C3, C1, any wCDM/CPL screen hit) should need no bespoke witness; count runs spent on witnesses.

## 2026-10-30 · experiment (annex LIV) · auxiliary function for non-polynomial laws
- Problem: CPL law has a real power and an exponential, not a polynomial identity. Change: one auxiliary g with its exact chain-rule identity, both differentiated, solved at t₀ without division (`scripts/gen_cpl.py`). Effect seen: whole theorem compiled after 3 local iterations (one fix was a `Pi.mul_apply` simp lemma, one a heartbeat limit). Keep.

## 2026-10-30 · process note · commit attribution
- Earlier commits of this run (d1e3bb4…e3d4606) lack the session attribution trailer the environment asks for; later commits carry it. No history rewriting (48.3); recorded here.

## 2026-10-30 · run 2026-10-30T0628Z · third verified finding F3
- C3 → **F3**: Capozziello, Cardone, Salzano 2008 (arXiv:0802.1583v2) Eq. (A2): lookback-distance D⁴_z has 7/2 q₀⁴, correct 7/8 q₀⁴; paper's d_L, d_A unaffected; misprint reprinted in arXiv:0902.0088 Eq. (25), 1104.3096 Eq. (A2), 1205.3421 Eq. (10.25).
- Frozen 362315b, 76227bf → PROVED in Work (374dee3 CI 41016090351 green; ee4fd5b) → AUDITED (`runs/2026-10-30T0628Z/audit.md`; blind restatement closed in Lean, `Work/Cosmography/CCSAudit.lean`) → promoted dac809b (CI: see STATE): `Checked.Cosmography.CCS.lookback_fifth_order`, `printedD4_fails`, `printedD4_fails_past`, `ccsD4Claim_false`, `ccsD4ClaimPast_false`.
- Referee: STANDS. Pipeline time for a candidate: one run (freeze → PROVED general theorem → audit → referee → promotion).

## 2026-10-30 · experiment (annex LIV) · truncated-power series inversion
- Problem: distance–redshift series need composition/inversion of Taylor series; iterated `HasDerivAt` chains (F1/F2 method) grow fast and need heartbeat hacks. Root cause: differentiating compositions instead of composing expansions.
- Change: `taylor_isLittleO` + `inversion` lemma (truncated powers, sympy remainders, `ring` checks). Effect seen: general fifth-order lookback theorem in ~5 local iterations, 27 s elaboration, no heartbeat options.
- How to tell: C1 (d_Q) and M2/M3 (d_L) should reuse it with a new A/P; count iterations.

## 2026-10-30 · experiment (annex LIV) · hub screening
- Observation: the Bamba et al. 2012 review reprints both F2 and F3; 0902.0088 and 1104.3096 reprint F3. Errors propagate within one group's papers and its review. Change: PROMPT note; STATE next step screens the review's cosmography sections formula by formula. How to tell: findings per screened formula vs the 2026-10-30T0028Z broad screen.

## 2026-10-30 · process note · records and attribution
- STATE (run 0430Z) misstated C3's error (named the l₀ term); caught by sympy before any Lean work. PROMPT note: quote FINDINGS/crops, not memory.
- This run's commits before the records commit lack the attribution trailer (second run in a row). PROMPT note added. No history rewriting (48.3).
- Referee subagent read the arXiv abs listing via export.arxiv.org after WebFetch timed out (PROMPT lists it among routes not to use); no finding content relies on it. Next referee prompts: say "if arxiv.org/abs is unreachable, report it; do not use mirrors".

## 2026-10-30 · run 2026-10-30T0828Z · verified findings F4, F5
- C5 → **F4**: Bamba et al. 2012 (arXiv:1205.3421 v1–v3) Eq. (10.54): D²_{L,y} overall sign wrong (+ in upstream Cattoën–Visser 2007 Eq. 52); review's own d_A,y contradicts it. Frozen 6636035 → PROVED in Work 819f3be (CI 41032795335 green) → AUDITED (`runs/2026-10-30T0828Z/audit.md`, blind closed in `Work/Cosmography/BambaDLyAudit.lean`) → promoted c22016e (CI 41034616298 green: build, leanchecker, axiom-audit, nanoda): `Checked.Cosmography.BambaY.lumDist_y_third_order`, `printedD2y_fails[_past]`, `bambaD2yClaim[Past]_false`. Referee STANDS-WITH-CORRECTIONS (error holds for all curvature; not in Lean).
- C1 → **F5**: Cattoën–Visser 2007 Eq. (59) (also gr-qc/0703122, 0809.0537 Eq. 32): d_Q(y) y² prefactor 1/12 → 1/24. Frozen d18789a → PROVED in Work 63610cd → AUDITED (audit.md §C1, blind closed in `Work/Cosmography/CVdQAudit.lean`) → promoted 2d9e567 (CI 41036122533 green): `Checked.Cosmography.CVdQ.dQ_y_third_order`, `printedQ2_fails_past`, `cvdQClaim[Past]_false`. Referee STANDS-WITH-CORRECTIONS.
- C6, C7: second route done (referee's independent sympy to y⁵, Milne and open-dust Mattig exact checks): differences confirmed. Lean pending (curved S_K).
- Correction: `source_C1.md` first cited d_Q as Eq. 3 (it is Eq. 5); `typeset/C5_p110_Omega0_def_eq10.52-53.png` shows only the Ω₀ definition (name overstates). Corrected in text, files kept.

## 2026-10-30 · experiment (annex LIV) · evaluation of run 0628Z experiments
- Truncated-power method: reused for d_L(y) and d_Q(y) (both theorems ≤ 10 local iterations each). KEEP.
- Hub screening: C5 from the hub screen became F4 in one run; C6, C7 confirmed. KEEP.
- Commit attribution note: every commit of run 0828Z carries the trailer. KEEP.

## 2026-10-30 · experiment (annex LIV) · heartbeat trap and MVT tool
- Problem: main d_L(y) proof timed out (whnf, 2M heartbeats) with no error location; ~25 min lost bisecting. Root cause: `fun_prop`/`Tendsto` ascriptions on large generated polynomials inside a context full of `set` variables. Change: standalone continuity/boundedness lemmas; PROMPT note with bisection advice. Effect seen: elaboration 3.5 min → 25 s, no heartbeat option. How to tell: next generated-polynomial proofs should need no heartbeat options.
- New tool `littleO_of_hasDerivAt` (integrals, real powers via MVT). How to tell: C6/C7 (S_K(χ) expansions) and z-versions of d_L should reuse it without new analysis lemmas.

## 2026-10-30 · run 2026-10-30T1028Z · verified finding F6
- C6 → **F6**: Bamba et al. 2012 (arXiv:1205.3421 v1–v3) Eqs. (10.55)–(10.57), verbatim from Capozziello & Salzano 2009 (arXiv:0902.0088) Eqs. (56)–(58): printed − correct = −(Ω₀−1)(3q₀−2)/6 (D³), −(Ω₀−1)²/120 − 5q₀(Ω₀−1)/12 (D⁴). Frozen b485344 → PROVED in Work be8b84d → AUDITED (`runs/2026-10-30T1028Z/audit.md`, blind closed in `Work/Cosmography/BambaCurvedAudit.lean`) → promoted to `Checked.Cosmography.BambaK` + `Checked.Cosmography.Transverse` (CI in STATE).
- Correction (referee, rendered page): F4's sign error is already in 0902.0088 Eq. (55); FINDINGS F4 "introduced in the review" was wrong; corrected by a note in F6 and F4's row kept.

## 2026-10-30 · experiment (annex LIV) · truncated-series algebra
- Observation: every d_L/d_Q/lookback theorem so far rebuilt remainder chains by hand (third order took ~10 iterations; one ~25-min heartbeat trap). Change: generic `approx_mul`/`approx_pow` (f ≈ p :⇔ f − p(X) = o(X⁵)), so a series proof is a list of sympy identities `p·r = m + x⁶W` plus one coefficient identity. Effect seen: fifth-order curved d_L(y) compiled after 4 local iterations (~15 min), all errors trivial. How to tell: C7 (d_A) and the z-series (C9) should each take ≤ 3 iterations reusing it.
- Pitfall found: `unfold A B` processes names in order, so a definition introduced by unfolding B is not unfolded by an earlier A; list outer definitions first. PROMPT note.

## 2026-10-30 · process note · referee file hygiene
- The referee wrote ~20 MB of third-party PDFs and full-page renders into `runs/…/referee/`. Moved to the session scratchpad before commit (never committed); only crops kept in `typeset/`. Change: PROMPT note; referee briefs must say "PDFs and full pages in a temp dir, crops only in the repo".

## 2026-10-30 · run 2026-10-30T1028Z · verified finding F7
- C7 → **F7**: Bamba et al. 2012 Eqs. (10.61)–(10.63) (verbatim from 0902.0088 Eqs. 62–64): printed − correct = −q₀(Ω₀−1)/4 (D³_{A,y}), −(Ω₀−1)[(Ω₀−1) + 10j₀ − 45q₀² + 20q₀]/120 (D⁴_{A,y}). Frozen 4337b9b → PROVED in Work 8e2df42 (headline compiled on the first attempt as a corollary of F6's theorem) → AUDITED (audit.md §C7, blind closed in `Work/Cosmography/BambaAngularAudit.lean`, referee STANDS) → promoted to `Checked.Cosmography.BambaA` (CI in STATE).
- Note: the C7 referee said both `all_goals ring` lines were dead; one was needed (compile failed when removed). Lean, not the referee, decides.

## 2026-10-30 · run 2026-10-30T1232Z · verified finding F8
- C9 → **F8**: Bamba et al. 2012 Eqs. (10.43)–(10.44), (10.50)–(10.51) (verbatim from CS 2009 Eqs. (31)–(52)): z-series D⁴_L, D⁴_A miss +k²/120, k = Kc²/(H₀²a₀²). Frozen 8c553aa → PROVED in Work 974b7a3 → AUDITED (`runs/2026-10-30T1232Z/audit.md`, blind closed 0314608) → promoted to `Checked.Cosmography.BambaZ` (CI in STATE). Referee STANDS-WITH-CORRECTIONS (provenance, origin Visser 2004 Eq. 40, size).
- Sec. XI screen: candidates C11–C14 (FINDINGS), F2 reprint (11.38) traced to Capozziello, Cardone, Salzano 2008 Eq. (40). C10 second route.

## 2026-10-30 · experiment (annex LIV) · evaluation of run 1028Z experiments
- Truncated-series algebra: not needed for C9 — an exact rational identity (1+z)⁵[S_y(z/(1+z)) − S_z] = z⁶W plus a transfer lemma did it; headline compiled on the second local attempt (one trivial tactic fix). KEEP (and the corollary pattern: new series from proved series by exact identities).
- `unfold` order: no failures this run. KEEP. Subagent file hygiene: all three subagents kept PDFs/renders out of the repo (screen 332 KB of crops/scripts). KEEP.

## 2026-10-30 · experiment (annex LIV) · start the referee at freeze time
- Problem: subagents run synchronously; this run blind (9 min) and screen (16 min) ran in parallel, but the referee ran alone afterwards and took 48 min, the largest single block of the run. Root cause: the referee was started only after proofs; but its main work (independent derivation, provenance, prior art, statement attack) needs only the frozen statements.
- Change: PROMPT note: launch blind restatement, referee and any screen together right after the freeze commit; the referee attacks the frozen statements, the main session then checks the proofs. How to tell: next finding's run has no serial referee block.

## 2026-10-30 · run 2026-10-30T1428Z · verified finding F9
- C13 (+ C11) → **F9**: Bamba et al. 2012 (arXiv:1205.3421 v1–v3) Eq. (11.31), from Capozziello, Cardone, Salzano 2008 (arXiv:0802.1583 v1/v2) Eq. (33): correct R − printed R = −2(3j₀²q₀ + 10j₀² + 11j₀q₀² + 4j₀q₀ + 90q₀²); printed F(R₀) formula (11.21) fails the paper's ΛCDM check (11.40) at every Ω ∈ (0,1); (11.13) sign of 2(q₀+4)j₀. Frozen 4ff3816 → PROVED in Work 1df6387, 5adf870 → AUDITED (`runs/2026-10-30T1428Z/audit.md`, blind closed c849eb5) → promoted to `Checked.Cosmography.FRCosmo` 2d0fae5 (CI in STATE). Referee STANDS. C12, C14: second routes.

## 2026-10-30 · experiment (annex LIV) · evaluation of run 1232Z experiments
- Subagents at freeze time: blind (21 min) and referee (13 min) ran in parallel right after the freeze; no serial referee block; proofs started after both returned, nothing redone. KEEP. Residual cost: the session is blocked while they run (≈ 21 min idle). Next: prepare the generator scripts (sympy certificates) before the freeze commit so the post-freeze work is pure Lean.
- Series transfer by exact identities: not exercised (no new series this run).

## 2026-10-30 · experiment (annex LIV) · HasDerivAt combinators must mirror the parse tree
- Problem: 5 failed local compiles in this run came from `exact (combinator).congr_deriv (by ring)` where the combinator's function was not syntactically the target function (`c * f * g` needs `(hf.const_mul c).mul hg`, not `(hf.mul hg).const_mul c`; sums are left-associated). Lean then elaborates `ring` against an unassigned metavariable and reports "ring failed … = ?m". Second source: `HasDerivAt.mul` and friends leave Pi-applications `(f * g) t`, which need `Pi.mul_apply`, `Pi.sub_apply`, `Pi.div_apply` before `ring`.
- Change: PROMPT working note. How to tell: next derivative-chain proof compiles with ≤ 2 such errors.

## 2026-10-30 · run 2026-10-30T1628Z · verified findings F10, F11
- C14 → **F10**: Bamba et al. 2012 (11.42)–(11.45) (from 0802.1583 Eqs. (43)–(44); reprinted 0902.0088 (107)–(108)): correct first-order η₂₀, η₃₀ coefficients −2(27Ω²+24Ω−32)/(27Ω(Ω−2)(27Ω²+60Ω+112)), −2(81Ω²−60Ω−16)/(243Ω²(Ω−2)(27Ω²+60Ω+112)). Frozen a164886 → PROVED in Work 8b1301e → AUDITED (`runs/2026-10-30T1628Z/audit.md`, blind closed fc4a51f) → promoted `Checked.Cosmography.FREta` f258555, CI 41093965309 green (incl. nanoda). Referee STANDS-WITH-CORRECTIONS.
- C15, C16 → **F11**: Demianski et al. 2017 (1609.09631) flat D⁴_L −105q₀⁴ (→ +105), D⁴_A +137j₀ (→ −137); D⁴_L reprinted in Lusso et al. 2019 (1907.07692). Frozen ab63005 → PROVED in Work 40619cb → AUDITED (`runs/2026-10-30T1628Z/audit_c15.md`; blind proved all its refutations, same transcription in `DemianskiZAudit`) → promoted `Checked.Cosmography.DemianskiZ` 21729d5 (CI in STATE). Referee STANDS-WITH-CORRECTIONS. Found by a new-hub screen launched at the C14 freeze; refuted in ~15 min with the Checked F8 theorems.
- Screen of the log-polynomial quasar cosmography hub: every coefficient relation used in the > 4σ tension tests and in the critiques AGREES (negative result recorded); minor C17, C18.

## 2026-10-30 · experiment (annex LIV) · evaluation of run 1428Z experiments
- HasDerivAt combinators mirror the parse tree: not exercised (this run's derivatives went through `hasDerivAt_mul_cont`, continuity only). Keep the note.
- Generator before freeze (1232Z follow-up): `gen_eta.py` written before the C14 freeze; post-freeze work was pure Lean (3 local compiles to close all eight headlines). KEEP.

## 2026-10-30 · experiment (annex LIV) · screen a new hub at every freeze
- Problem: the session idles while blind and referee run (≈ 10 min this run, 21 min in 1428Z), and the Bamba hub is exhausted (STATE). Root cause: subagent time was spent only on the claim in hand.
- Change: PROMPT note: in the same message as blind + referee, launch a screen of a new source family; its candidates are checked against the Checked general theorems right away. This run: the screen found F11 in the same run. How to tell: next runs keep producing candidates from new families without a dedicated screening run.

## 2026-10-30 · experiment (annex LIV) · transcriptions must reproduce the paper's own numbers
- Problem: the (11.43) numerator bracket was misparsed twice by subagents (1428Z referee `ref_eta.py`, 1628Z blind). Root cause: nested brackets across a fraction are ambiguous in a crop; nobody checked the transcription against the printed numbers until later.
- Change: PROMPT note and brief rule: when the source prints numbers computed from a formula, the transcription must reproduce them before it is used. How to tell: no further misparse reaches a Lean file or a report.

## 2026-10-30 · experiment (annex LIV) · local build scope and `field_simp`
- `lake build Work` locally exceeded the 2-min tool limit (other Work modules not cached). Build named modules (`lake build Work.Cosmography.X`) with an explicit timeout. `field_simp` left Ω⁻¹ / reordered cubics unsolved twice; `rw [div_eq_div_iff …]` / `div_sub_div` then `ring` closed them first time. PROMPT note.

## 2026-10-30 · Alexander's instruction (chat, after run 1628Z) · "the real goal is big, don't lose it"
- Recorded as PROMPT standing instruction 9 (big-track rule: one-line big-track answer in every run record; big track gets the main block of at least every other run; presentational misprints parked unless cheap). New section "Big track" in TARGETS.md with B1 (truncation of cosmographic Hubble-diagram fits vs the > 4σ ΛCDM tension claim: settle the mathematical half by proof) and B2 candidates. STATE next step updated. Experiment (LIV): a later daily review checks whether runs since this change produced progress on B1 (frozen statement, certified enclosures) and not only misprints.

## 2026-10-30 · Alexander's instruction (live, during run 1828Z) · the goal is the trust system
- Verbatim: "Making fields checkable. Specifically, formalization: turning maths, physics and chemistry into forms a machine can verify (proofs in Lean, rigorous simulators, test suites for scientific claims). By that I mean making a program, system, proof, whatever, that allows scientists to trust AI to do scientific work without outside verification." He called the earlier big-track reading (settle one physics question) too narrow.
- Recorded as annex 36.0, operative-core goal line and closing question, PROMPT standing instruction 9 (replaced), TARGETS.md "Trust track" T1–T5 (B1/B2 kept as demonstrations). Run 1828Z redirected its main block from B1 certified numerics to T1 (machine-checked definition specs + mutation benchmark).
- Experiment (LIV): every run record states what a scientist can now trust without checking; a later daily review checks that the kill-rate metric exists and moves.

## 2026-10-30 · run 1828Z · experiment (annex LIV) · machine-checked definition fidelity
- Root cause addressed: definition fidelity (XXXVII) was guarded only by prose (TRUSTED_DEFINITIONS) and same-model subagents, so nothing machine-checked stopped a wrong definition under a correct proof.
- Change: spec predicates + `*_meets_spec` + blind mutation benchmark + spec-aware adversary + pinning theorems (`Work/Fidelity/`), metric script, PROMPT working note.
- Observed: anchor-only specs kill blind mutants (30/30) but leak to an adversary (4 gaps in minutes); specs with general laws pin. Decision: the standard for a trusted definition is a pinning theorem, not a kill rate.
- Evaluate (later run): do promoted pins exist in Checked, does CI report unpinned definitions, and does an adversary on `FlatLCDMSpec` find gaps.

## 2026-10-30 · run 2028Z · integrity event (annex 39.5): CI step added (strengthening only)
- New step in the `checked` job: `lake env lean scripts/trust/StatementDeps.lean`. It computes, for every headline in `scripts/trust/headlines.txt`, the program definitions its statement rests on and writes `TRUST_MAP.md`. Blocking: a headline, pin or kind entry that does not resolve to exactly one Checked constant; a pin theorem whose statement does not mention its definition. Informational: unpinned physics definitions; stale committed `TRUST_MAP.md` (warning). No existing check changed.
