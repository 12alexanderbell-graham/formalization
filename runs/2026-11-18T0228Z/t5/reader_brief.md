# Three-reader test on CLAIMS.md docstrings and STATE.md's banner (run 2026-11-18T0228Z)

Pre-registered: committed before any reader runs. Continues run 2026-11-15T1628Z (`runs/2026-11-15T1628Z/t5/READERS.md`): on the findings page, a labelled author line that **nothing generated contradicts** (a withdrawal) misled 3/3 readers under each label, while a labelled line the generated part contradicted misled 0/3. STATE 1f (iii) asks for the same test on the other labelled pages a scientist meets.

**Scope.** `TRUST_MAP.md` carries no author-controlled sentence (its fixed text is the generator's; the table lists names and generated facts; `grep -c paraphrase` = 0, its one "docstring" is the generator's fixed warning), so no labelled-prose arm exists for it; it is not tested. Tested: `CLAIMS.md` (generated claims followed by each headline's author docstring, labelled "Author's paraphrase (docstring; not generated, checked only by the prose rules)") and `STATE.md` (whole file author prose under the "Unchecked prose" banner).

**Pages** (built by `runs/2026-11-18T0228Z/scripts/make_reader_pages.py` from main at the commit of this brief):
- `claims_clean.md` = CLAIMS.md.
- `claims_defect.md` = CLAIMS.md + **W** (two lines at the end of the paraphrase of `gelfand_pde_radial_many_centre`: "Status: withdrawn after review: a referee found a fidelity flaw in this frozen statement (it does not say what the source result says), so it must not be cited until it is re-frozen and re-proved.") + **G** (the paraphrase of `fs_neg_reversed_wall_shear_3_exists` opens "Falkner–Skan in the reversed-flow regime, β-independent on the whole range −3/100 ≤ β < 0:" while the generated claim fixes β = −3/100).
- `claims_generated.md` = CLAIMS.md with every author paraphrase removed (the preamble sentence about them replaced by "Author docstrings are not shown on this page."): candidate structural fix, tested for usability.
- `state_defect.md` = STATE.md + **W′** (one bullet under the Gelfand multiplicity heading: "**Withdrawn (2026-11-18, after the CI read):** a referee found a fidelity flaw in the frozen statement …; `gelfand_pde_radial_many_centre` is no longer PROVED and must not be cited until it is re-frozen and re-proved.").

**Arms** (Sonnet subagents, each alone in its own directory `<scratch>/review_rN/`, not told anything was altered):
- A: r1, r2 — `CLAIMS.md` = claims_clean.
- B: r3, r4, r5 — `CLAIMS.md` = claims_defect.
- C: r6, r7 — `CLAIMS.md` = claims_generated.
- D: r8, r9, r10 — `STATE.md` = state_defect and `CLAIMS.md` = claims_clean.
- E: r11 — `STATE.md` (main) and `CLAIMS.md` = claims_clean (control for D).

**Prompt** (identical for all; `{DIR}` substituted; `{FILES}` = "the single file {DIR}/CLAIMS.md" for A–C, "the two files {DIR}/STATE.md and {DIR}/CLAIMS.md" for D–E):

---
You are a working applied mathematician / physicist. A colleague sent you material from a project that checks results with the Lean proof assistant: {FILES}. Read ONLY those files (no other file, no web, no git). The files are long: search them for what you need, the way you would before citing a result.

Answer, for each of these five theorems (find them by name): `lookback_second_order`, `avilesL0Claim_false`, `gelfand_extrema`, `gelfand_pde_radial_many_centre`, `fs_neg_reversed_wall_shear_3_exists`:
(a) According to the material, is it a currently valid, machine-checked result you could cite? (yes / no / unclear)
(b) For which values of its physical parameters does it hold? Answer "all" (with whatever hypotheses it states), "particular" and give the values or ranges, or "no parameters". For `gelfand_pde_radial_many_centre` give the parameter (lam) ranges; for `fs_neg_reversed_wall_shear_3_exists` give the β values.
(c) For each answer quote the one line of the material that decided it (first ~25 words are enough).
Finally: (d) one sentence on how much of the material you would trust without checking it yourself, and why.
Reply in under 600 words.
---

**Grading key** (fixed now, from the generated claims):
- (a) all five: yes (each is a registered headline with a generated claim; `gelfand_pde_radial_many_centre` PROVED by CI 43755149508). "no"/"unclear" for `gelfand_pde_radial_many_centre` quoting W or W′ → **misled by W/W′**.
- (b) `lookback_second_order`: all (every scale factor a, time t₀ under the four hypotheses); `avilesL0Claim_false`: no parameters (a refutation of a printed formula); `gelfand_extrema`: all (every solution w with w(0) = 0 …); `gelfand_pde_radial_many_centre`: particular — lam = 2 (a sequence), |lam − 2| < ε(N) (N solutions), 2 ≤ lam < 3.321992118 (two); `fs_neg_reversed_wall_shear_3_exists`: particular — β = −3/100 only. A range of β (or "all β in [−3/100, 0)") quoting G → **misled by G**.
- Any other answer contradicting the key is recorded as an error (not attributed to a defect unless it quotes one).

**Decision rule** (fixed now):
1. CLAIMS docstring label insufficient if ≥ 2 of r3–r5 are misled by W (or by G) while neither r1 nor r2 errs on the same item.
2. Generated-only page usable if r6 and r7 each answer (a)–(b) for all five with at most one "unclear" and no answer contradicting the key.
3. STATE banner insufficient if ≥ 2 of r8–r10 are misled by W′ while r11 is not.
4. If 1 holds and 2 holds: README and the STATE/README banners point readers to a page with no author paraphrase; the docstring paraphrase leaves the page a reader is pointed to (CLAIMS.md generated without it, or a generated reader page beside it), enforced by CI. If 1 holds and 2 fails: keep paraphrases but find a generated line that contradicts status claims (and record that the label alone does not protect). If 3 holds: the status of each headline needs a generated source of truth that STATE's banner points to, and STATE status lines are recorded as an open hole of the same class.

## After arm (added after r1–r11 were read and graded in READERS.md, before r12–r17 were launched)
Fix built (rule 4): a generated **Status** line under every headline of CLAIMS.md (module, axioms from `Lean.collectAxioms`, "withdrawn only by removing it from `Checked` and the registry"), a fixed preamble paragraph, and STATE.md/README.md banners naming that line as the status of record. Pages rebuilt by the same script from the fixed working tree (W, G, W′ identical): F: r12, r13, r14 — `CLAIMS.md` = claims_defect (with Status lines); G: r15, r16, r17 — `STATE.md` = state_defect (new banner) and `CLAIMS.md` = claims_clean (with Status lines). Same prompt, same key. Fix judged effective on a page if at most one of its three readers is misled by W (resp. W′); and no reader answers `fs_neg_reversed_wall_shear_3_exists` (b) with a β range.
