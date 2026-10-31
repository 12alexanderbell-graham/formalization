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

## 2026-10-30 · run 2028Z · evaluation of run 1828Z experiment (machine-checked definition fidelity)
- Promoted pins exist in Checked: yes (and 8 more this run). CI reports unpinned definitions: yes, since this run (trust map step). Adversary gaps on `FlatLCDMSpec`: closed by a pinning theorem against a blind first-principles formulation rather than by more anchors. KEEP; standard confirmed: pin by a general law, anchors cross-check the law.

## 2026-10-30 · run 2028Z · experiment (annex LIV) · trust map: which definitions do the headlines actually rest on?
- Problem: the trust claim "4 of 5 central definitions pinned" (run 1828Z) was a hand-picked list; nobody had computed which program definitions the headline statements use. Root cause: dependency of statements on definitions was tracked in prose (TRUSTED_DEFINITIONS), not by machine.
- Change: `scripts/trust/StatementDeps.lean` (Lean metaprogram over the compiled environment: statement → definitions, transitively, stopping at pinned ones), registries `headlines.txt`, `pins.txt`, `def_kinds.txt`, generated `TRUST_MAP.md`, CI step (registry errors block; report informational; stale-map warning).
- Observed: at first run 15/88 headlines rested only on pinned definitions; the two most-used definitions were unpinned. After targeting them: 63/82 physics headlines.
- Evaluate (later run): does every new headline get added to `headlines.txt` (else the map silently shrinks — consider a CI check that every `theorem` cited in STATE "Results" is listed); did the control run fail as required; make the UNPINNED report blocking for new headlines once the F(R)/CPL backlog is closed.
- Run 2028Z, same day: control run 41128703059 on `control/bad-pin-registry` FAILED at the trust-map step for the right reason (pin theorem does not mention the definition). The registry check bites. By run end: 17 definitions pinned, 77 of 82 physics headlines rest only on pinned definitions; unpinned: `dQFlat` (a convention, d_Q = d_L/(1+z)^{3/2}, no independent law), `transverse` (helper).

## 2026-10-30 · run 2228Z · integrity event (annex 39.5): CI check strengthened (non-vacuity witnesses)
- The trust-map step (`scripts/trust/StatementDeps.lean`) now also fails CI when a headline whose statement has a hypothesis (or a binder that is not plain real/natural data) has no **non-vacuity witness**: a `Checked` theorem whose statement is syntactically `Checked.Trust.nvObligation` of the headline (every binder and hypothesis turned into `∃`, conclusion dropped; a trailing negated hypothesis `P → False` is the conclusion and is dropped). Obligation code: `Checked/Trust/NonVacuity.lean`; witnesses: `Checked/Trust/Witnesses.lean`. Only adds a check; no existing check changed. Step renamed accordingly.

## 2026-10-30 · run 2228Z · experiment (annex LIV) · statement fidelity T2a: machine-checked non-vacuity
- Problem: non-vacuity of headline statements ("the hypotheses can hold together") was checked by audit subagents in prose, once, at promotion; nothing stopped a later edit, and the 17 pinning theorems (`spec D → D = def`) are vacuous if their spec is inconsistent, which no check tied to the pin. Root cause: statement fidelity was a review activity, not a computed obligation.
- Change: obligation computed from the statement by a 40-line metaprogram, witnesses proved in Lean, CI blocks a conditional headline without a witness. Pin witnesses use the definitions' own `*_meets_spec` proofs, so every pin's spec is now machine-checked satisfiable.
- Observed: 100 headlines; 57 conditional, 57 witnessed (all on the first build but one tactic); 43 unconditional (refutations of source claims, closed identities). No vacuous headline found.
- Evaluate (later run): did the control run fail for the right reason; does every new headline arrive with a witness (CI forces it); next T2 step: hypothesis necessity (for each hypothesis, a Checked counterexample showing the conclusion fails without it, or a note that it is a domain condition).

## 2026-10-30 · run 2228Z · integrity event (annex 39.5): unpinned physics definitions now block CI; obligation generator hardened
- After `transverse` was pinned (`Checked/Fidelity/TransverseSpec.lean`, blind ODE law, uniqueness via Mathlib `ODE_solution_unique_of_mem_Ioo`) and `dQFlat` was reclassified PRINTED (a source convention, d_Q := d_L/(1+z)^{3/2}, Cattoën–Visser Eq. 5, built from pinned `lumDistFlat` and `redshift`), every headline rests only on pinned definitions. The trust-map step now fails CI when a headline rests on an unpinned PHYSICS or UNCLASSIFIED definition (planned in run 2028Z's experiment: "make the UNPINNED report blocking once the backlog is closed").
- Non-vacuity obligation hardened after an adversarial subagent review (`runs/2026-10-30T2228Z/nv_adversary.md`): unfold `Checked` definitions at the head, split `∧`, require one side of `↔`, reject `¬ ∃`, drop a trailing binder before `False` only if it is a proposition, plain types = types with a `Nonempty` instance. Four new witnesses (the `program ↔ blind` equivalences). Strengthening only.

## 2026-10-30 · run 2228Z · evaluation of run 2028Z experiment (trust map)
- Control run failed as required: yes (41128703059), and two new controls this run (41140145749, 41142047810) failed for the right reasons. UNPINNED report made blocking: done (backlog closed). Not done: a check that every theorem cited in STATE "Results" is in `headlines.txt` (a headline left out escapes all three checks). KEEP; carry the missing check to a later run.

## 2026-10-31 · Alexander's instruction (chat, after run 2228Z) · the publishable result is the goal itself; no narrowing
- Asked whether the program could reach "a real publishable result", the session answered with a misprint paper, a methods paper and a "scoped version" with pessimistic run counts. Alexander: the publishable result means publishing the successful goal; "please reread the … constitution, you specifically keep confidence, you specifically remember nothing solid is keeping you in a scope and preventing you from doing anything, stop narrowing shit down and deciding only part of something is possible."
- Root cause (annex LIV): a repeated pattern of shrinking the goal to what looks safely reachable (earlier the same day the big track was read too narrowly, corrected by Alexander at ~18:45Z). It contradicts the original II (capability directive), 2.3 (do not lower ambition because the problem is difficult), 17.3 (reject exactly what the evidence rejects), 30.2 (do not manufacture pessimism).
- Change: PROMPT standing instruction 10; `TARGETS.md` section "THE RESULT" (the full demonstration: every link machine-checked incl. numerics, simulators and data claims; AI doing new science through the system; measured false-acceptance rate; one-time expert validation; maths, physics and chemistry); operative-core line.
- Experiment: the next daily review checks that run records and plans state the full goal and the next decisive step, with no narrowing or invented pessimism.

## 2026-10-31 · integrity event (annex 39.5): CI job `goal-guard` added (strengthening only)
- Alexander: "better not lose that, you already lost it maybe thrice" (the full goal as the publishable result; no narrowing). Root cause: the goal lived as one item among growing working notes, and nothing failed when a run or a chat answer drifted from it.
- Change: goal block at the top of `PROMPT.md`; `scripts/goal_guard.py` (new CI job) fails if the goal or the no-narrowing instruction disappears from PROMPT (first 30 lines), the operative core, TARGETS ("THE RESULT") or STATE, or if a run record from 2026-10-31T0100Z on lacks its `**THE RESULT:**` front-page line. Run 0028Z (in progress under LOCK) is exempt by date; STATE not touched (48.4).

## 2026-10-31 · run 0028Z · experiment (annex LIV) · T5: first measured false-acceptance rate of the trust pipeline
- Problem: every trust metric so far (pins 101/101, non-vacuity 62/62, second reading 36/38) counted what the checks *cover*; nobody had measured what wrong science the pipeline *accepts*. THE RESULT (part 3) requires that number. Root cause: checks were designed and judged by the model that built them; no adversary of a different model, no seeded defects.
- Change: red teams of a different model (Sonnet) wrote 24 seeded defects (A: 8 honest mistakes; B: 8 adversarial against the 2228Z checks; C: 8 adversarial against this run's strengthened checks), each `apply.py` + `claim.md`; local judge applies each to a clean tree, builds, runs the CI-replica checks before and after, restores (`runs/2026-10-31T0028Z/t5/`).
- Observed: checks as of 2228Z accepted 15 of 15 valid A+B defects (A08 invalid: missing import). Strengthened checks (v2): 6 of 15 accepted (A03, A04, A05, A06, B04, B07: new definitions labelled FORMULA, prose numbers/scope, an existential headline). Red team C found 8 holes in v2 within minutes; v3 closed 6 of them before judging: under v3, C accepted 2/8 (C02, C06); all 8 had passed the 2228Z checks. Totals: 23/23 valid defects accepted before, 8/23 after. v4 (pin shape: load-bearing SPEC only) targets C02, not yet re-judged. Decision: KEEP the benchmark as a standing test set; holes that need new mechanisms (records generated from Lean, physics-named definitions) are next steps, not patches.
- Evaluate (later run): rerun A, B, C (and a fresh red team D against v3) after every change to the checks; the rate must go down, not the defect difficulty. Do the C-round holes get closed? Track the accepted fraction per category in STATE.

## 2026-10-31 · run 0028Z · integrity event (annex 39.5): CI checks strengthened (frozen registry, unused binders, pin shape, records, imports, stale map)
- `scripts/trust/StatementDeps.lean` now also fails CI when: a headline, pin theorem, pinned or classified definition differs from its fingerprint in `scripts/trust/frozen.txt` (statement; for definitions statement + body + kind) or a frozen entry is no longer registered; a headline or pin has a binder (other than an instance) its proof never uses, looking through proofs that are other Checked theorems; a pin's statement uses no SPEC-kind definition independent of the pinned definition; a theorem cited in STATE.md or FINDINGS.md whose statement uses program definitions is not a registered headline; Checked imports a `Work` module. Private definitions are now reported (they were invisible to the trust map).
- New CI step `scripts/trust/check_relock.py`: a push that changes or removes a frozen entry must add a LEDGER.md line naming it (whole word). Checkout now fetches full history for it.
- A stale committed `TRUST_MAP.md` now fails CI (was a warning).
- Baseline: all 101 headlines and 19 pins pass every new check unchanged (no unused binders, all pins have an independent spec, 101 record citations registered or pure mathematics); `frozen.txt` holds 239 entries.
- Only adds checks; no existing check changed or weakened.

## 2026-10-31 · run 0028Z · evaluation of run 2228Z experiment (T2a non-vacuity)
- Control failed for the right reason: yes (2228Z). Every new headline arrives with a witness: no new headline since; CI forces it. Next T2 step (hypothesis necessity): its level 0 is done this run (unused binders are a CI error; baseline clean). T5 shows the remaining statement-fidelity holes: an existential conclusion (A05), a hypothesis bundled in a conjunction and only partly used (C06), a statement that is weaker than the prose (A03). KEEP.
- Correction (same run, 02:20Z): the local judge built only `Checked`; CI also builds `Work`. Control run 41158182668 (B02, relocked, no LEDGER) failed in CI at the Work build (axiom-audit step; `LookbackAudit.lean` uses the old statement), before check_relock. The before-counts (23/23) are upper bounds for CI; the judge must build Work too (next run).

## 2026-10-31 · run 0228Z · integrity event (annex 39.5): certified numbers in FINDINGS.md (CI strengthened)
- Problem (T5, run 0028Z): wrong numbers written into FINDINGS.md (red-team defects A06: l₀ = 3.151 for 3.115; B07: η₂₀ = −0.149ε for −0.249ε) passed every check; records were prose.
- Change: `Checked/Records/Basic.lean` (`RoundsTo x d k`: x rounds to d at k decimals; `exists_root_roundsTo`, IVT), `Checked/Records/Findings.lean`: 14 registered headlines certifying the 26 computed decimals of the verified findings, stated where possible for *every model* through pinned definitions (e.g. `F1_l0`: every flat ΛCDM model with Ω_m = 3/10 has cosmoCoeff 5 rounding to 3.115; `F3_D4_LCDM`, `F2_toy`, `F2_error`), otherwise as values of the printed/derived formulas. `scripts/trust/StatementDeps.lean` extracts every `RoundsTo` literal of a `Checked.Records` headline into `.lake/records_numbers.tsv`; new CI command `scripts/trust/check_numbers.py` fails if a decimal (or ≈/≃ number) in "Verified findings" is untagged, or a `[✓name]` tag does not match the certified literal exactly. Other tags, shown to the reader: `[src]` quoted from the source, `[in]` chosen input, `[unc]` computed but unchecked.
- New kind `MATH` (pure-mathematics predicate) for `RoundsTo`; `FREta.Jfam` classified COMPOSITE. frozen.txt: 16 new entries, no existing entry changed.
- Baseline: 57 tagged numbers: 26 certified, 19 quoted, 10 inputs, 2 unchecked (F2's figure-crossing redshifts 1.35, 1.07: referee numerics). Tested: A06/B07-style edits fail with the certified value named.
- Only adds checks; no existing check changed or weakened.

## 2026-10-31 · run 0228Z · records correction found by the new check
- F11 said the l₀ shift absorbing the D⁴_L error is "≈ −87 at their q₀ = −0.80"; −210·(0.80)⁴ = −86.016 (`Checked.Records.F11_sizes`). Corrected to −86 in FINDINGS.md. No reported finding changes.
- F2 wording: "error 2·0.7·6.7·0.25 = 2.345" replaced by the certified "true − printed = 2(1−Ω_m)(7−Ω_m)w_a² = 2.345" (valid for every w₀, `F2_error`).

## 2026-10-31 · run 0228Z · integrity event (annex 39.5): certified-number and records checks hardened after red team D
- Red team D (Sonnet, 8 defects against the checks of this run, `runs/2026-10-31T0228Z/t5/redteamD/`) found, among others: a certificate by `¬ RoundsTo` (D05), a new `## ` heading that ended the scanned section (D06), an en dash read as a minus sign (D07), a power of ten outside the checked token (D03), citations of invented theorem names (D08).
- Changes (all strengthening): `StatementDeps.lean` takes only *asserted* `RoundsTo` (through ∀, →-conclusion, ∧, ∃; error if one sits under ¬/∨/↔ or in a hypothesis) and fails on a backticked dotted name in STATE/FINDINGS that lies in an existing Checked namespace but names no constant; `check_numbers.py` scans all of FINDINGS.md except the "Candidates under verification" section, reads every dash as a minus, and treats `1.3×10⁻⁵` as one number (power of ten before the tag).
- Frozen entry changed: `F8_sizes` now certifies the shift k²z⁴/120 itself (0.000013 at 6 decimals) instead of 10⁵ times it, so the prose `1.3×10⁻⁵[✓F8_sizes]` is checked including the exponent.
- Same run, later: hypotheses of headlines and pins may not be syntactic conjunctions (`StatementDeps.lean`; red team C, defect C06 bundled `decel a t₀ = −1` into a conjunction the proof used only partly, invisible to the per-binder unused check). Baseline: no headline or pin has one. Strengthening only.
- Same run, later (red team D, defect D02 changed the input Ω_m = 0.3 next to numbers certified at 0.3): inputs next to certified numbers are bound to their record, `0.3[in✓F1_l0]`, and must be one of the real numerals of the record's statement (`StatementDeps.lean` writes them to `.lake/records_params.tsv`); in a sentence with a certified number, bare [in]/[src]/[unc] are errors; (number, [in✓name]) pairs are protected like certified numbers. Frozen entry changed: `F3_D4_LCDM` now also certifies q₀ = −0.55 (added conjunct `RoundsTo (decel a t₀) (-0.55) 2`), so the prose input is certified rather than asserted.

## 2026-10-31 · run 0228Z · experiment (annex LIV) · records as certified data, not prose
- Problem: what a scientist reads (FINDINGS, STATE) was prose written by the model; T5 showed wrong numbers there pass every check. Root cause: the trust pipeline ended at Lean statements; the last link to the reader was unchecked.
- Change: numbers in FINDINGS are literals of registered Lean records (`RoundsTo`), tied by CI tags. First case of "records generated from / checked against Lean".
- Observed: 26 values certified on the first pass; one record error found (F11). Red team D found the boundary of the approach within minutes: tags certify a value, not its prose label (D01), and a record of a free formula certifies only arithmetic (D04).
- Evaluate (later run): after generated sentences/claim sheet, re-run A–D; the accepted fraction for the misleading-record and wrong-number categories must fall to 0 or be shown to need prose that the reader is told is unchecked.

## 2026-10-31 · run 0228Z · evaluation of run 0028Z experiment (T5)
- Rerun after changes to the checks: done with judge v5 (CI-exact, Work build included) on the open set and on red team D (`runs/2026-10-31T0228Z/t5/RESULTS.md`); the earlier "before" upper bound stays as recorded. The rate fell for the targeted classes (wrong numbers: A06, B07 and D02, D03, D07 caught; C06 caught after the conjunction rule), and the new red team found new holes, as the experiment predicted. Not done: full rerun of every 0028Z defect under v5 (queued in STATE).
