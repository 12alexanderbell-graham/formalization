# External test, targets 1, 2, 3 (standing instruction 11), run 2026-11-26T1529Z

Same method as `EXTERNAL_S.md`: source read literally → brief committed → fresh Sonnet blind reading
committed → closure of the reading against the frozen outside statement (in the outside project's own
Lean/Mathlib pin, statements taken with `type_of%`) → `scripts/external/coverage.py` → solution replay
(`scripts/external/replay.sh`, GitHub workflow `external.yml`). Files under `runs/2026-11-26T1529Z/T1|T2|T3/`.
Reviews and audits of these results were not read before the verdicts below were committed.

## Target 3 — AlphaEvolve's rank-48 algorithm for 4×4 complex matrix multiplication — **DONE**

- Source: google-deepmind/alphaevolve_results @4226acb, `mathematical_results.ipynb` (sha256 2cce2543…),
  cell "Rank-48 decomposition of <4,4,4> over 0.5*C"; the notebook's own check is floating-point numpy.
- Data: `T3/extract.py` parses the cell with `ast.literal_eval` (no code executed), doubles every entry to
  a Gaussian integer (all entries are exact multiples of 1/2: asserted), re-checks the identity exactly in
  ℤ[i] in Python, and the Lean data lists were regenerated and compared equal.
- Kernel certification (`T3/check.lean`): all 4096 entries of Σ_r U⊗V⊗W = 8·T⟨4,4,4⟩ in ℤ[i], 16 theorems
  `decide +kernel` (no `native_decide`), axioms: propext only; about 2 minutes.
- Algorithm over ℂ (`T3/closure.lean`): ∀ A B : Matrix (Fin 4) (Fin 4) ℂ, A * B = Σ_{r<48}
  (Σ a_r·A)(Σ b_r·B) • C_r; blind reading closed 2/2 (`reading_algorithm`: 48 products of linear forms;
  `reading_entries`: all coefficients in ½ℤ[i]). Axioms standard. Lean 4.34.1 / Mathlib d13f23b.
- Rests on judgment: only the blind reader's rendering (bilinear algorithm over commutative ℂ; the
  reader notes that use as a recursive block algorithm would need noncommutative validity, which is not
  claimed and not checked).

## Target 1 — OpenAI's Navier–Stokes blow-up (Clay alternatives (C) and (D)) — **NOT DONE** (statement level done)

- Source: Clay official problem text (Fefferman; fetched, equations as rendered), openai/NavierStokesAndEuler
  @f9e8bc5 `ComparatorChallenges/NavierStokes.lean` (adapted from DeepMind's formal-conjectures).
- Closure (`T1/closure.lean`, Lean 4.34.0-rc2 / Mathlib 85e3a25): frozen (C) ⟹ blind reading of Clay (C);
  frozen (D) ⟹ blind reading of (D). Bridged: the vector equation vs. the reader's componentwise (1)
  (∂_t by `derivWithin` on [0,∞), (v·∇)v, Laplacian through an orthonormal basis, gradient), divergence as
  the trace of the derivative, decay with real vs. natural exponents, energy with integrability. Coverage 2/2.
- Pins (`T1/pins.lean`): zero data satisfy the frozen data conditions and the zero solution satisfies the
  frozen solution notions on ℝ³ and the torus, so "no solution exists" is not true for a junk reason;
  `∞` in `ContDiff ℝ ∞` is C^∞, not ω.
- **Solution replay, partly done:** GitHub run 45880627629 (job 140118837233): the 610-module closure built in
  the pin (the Lean kernel accepted every declaration), and the declaration comparison found the two target
  statements and all 86 other reachable challenge declarations identical to the solution's, with axioms
  propext, Classical.choice, Quot.sound for both targets; it stopped on 9 private `local notation` syntax
  declarations of the challenge (not referenced by any statement; the comparison now skips unreachable
  declarations and lists them). **Blocking link:** the independent replays (leanchecker per module, nanoda)
  of that closure, re-dispatched after the fix; NOT DONE until they report.
  (The first attempt, run 45872140013, failed in our tool: copied `structure`s are new types — diagnosed in a
  chat session, fixed by `compare_decls.lean`.)
- Advisory scan: 65 `local notation` lines in the solution closure, no sorry/axiom/native_decide.

## Target 2 — "more than two thirds of the zeta zeros are simple and on the critical line" (Alpöge–Furman, argument by Claude; announced 41.6% → 67.2%) — **DONE** for the target claim (67.2%, counted as the paper counts) and Theorems 1–2 as stated; the paper's (0,T) rate remark is NOT DONE (no Lean statement)

- Source: arXiv 2608.13637 TeX (Theorem 1, Theorem 2, §1.1 definitions, the (0,T) sentence);
  anthropics/zeta-23-lean @11b6c7e `zeta23/Challenge.lean` (17 theorems).
- Closure (`T2/closure.lean`, Lean 4.33.0-rc2 / Mathlib 51e6992): frozen ⟹ blind reading of Theorem 1 (i),
  (ii), the Montgomery–Taylor constants (the paper's c_MT⁻¹ = ½ + cot(1/√2)/√2 proved equal to 1/cMT of the
  frozen closed form), the a-fortiori N₀* bound, Theorem 2 (including q = 1 through
  `LFunction_modOne_eq`; the frozen file assumes q > 1), and the **announced headline read literally**:
  N₀(0,T) ≥ (0.672 − o(1)) N(0,T), with 2 − 1/c_MT ≥ 0.672 certified (`T2/decimal.lean`: cos, sin of 1/√2
  by Mathlib's `Complex.exp_bound` to degree 7; the true value is 0.67250…).
- **UNCOVERED (finding, minor):** the paper states the (0,T) results "with rate O(log log T/log T)"; the
  frozen statements carry only o(1). That sentence of the paper is not machine-checked (coverage 6/7).
- Counting conventions checked: zeros with multiplicity on the N side, distinct zeros on the N₀* side (the
  conservative direction); windows by positive ordinate; zero counts are finsums/ncard, whose junk values
  on infinite windows cannot help the frozen statements (an infinite window makes N = 0, which is how the
  headline closure handles it without assuming finiteness).
- **Solution replay: PASSED** (GitHub run 45874989863, job 140099828860, 18:21–19:27Z): closure of `Solution` (190 modules) built in the pin; all 17 challenge theorems proved by the solution with axioms propext, Classical.choice, Quot.sound (match step; the challenge has only `def`s, for which the copy-and-prove match is sound); leanchecker on every module; nanoda: 72,933 declarations, no type errors. Re-run with the declaration comparison (`compare_decls.lean`): **PASSED** (run 45880627629, job 140118837261): COMPARE OK on every challenge declaration, standard axioms on all 17 targets, leanchecker 191 modules, nanoda 72,900 declarations.
- Advisory scan (after the nested-comment fix): no sorry, axiom or native_decide in the solution closure; 24 `set_option backward.*`, 6 custom syntax.
- Note: this result was produced at Anthropic, which also made the model running this audit; the
  procedure is the same as for the other targets.

## Time

T3: brief 18:00Z → DONE 18:14Z. T1: brief 17:07Z → closure 17:29Z. T2: brief 17:41Z → closure 17:57Z.

## After the verdicts: comparison with human reviews (read after commit c275b8f)

| target | humans found | system found | comparison |
|---|---|---|---|
| T1 | F. A. de Luca audit (github, pinned 8937a8f): own Clay spec + bridge, Comparator theorems ⟹ Clay (C)/(D), comparator/nanoda PASS, translation boundary named as the residual; incrediblecrab: rebuild + comparator two kernels + "trusted statement shown satisfiable"; Bastounis–Circelli–Hansen (arXiv 2610.08144): internal Lean lemmas differ from the written proof's lemmas (e.g. m+5 vs m+4 derivatives), no claim about the headline statement; zboi29 "counter-proof": by its own README a programme, not a completed disproof | frozen (C), (D) ⟹ blind reading of Clay (C), (D); zero data / zero solution pins (the satisfiability point); solution replay pending | **same finding as the human audits** at the statement level, reached independently (bridge + satisfiability). The NL-proof-vs-Lean-proof divergence is outside what the system checks: it certifies the stated theorem, not that the Lean proof follows the paper's argument — recorded as a scope note, not a defect of the result |
| T2 | Anthropic's AUDIT.md: 0 axiom declarations, `#print axioms` standard for 27 statements; third-party static audit (aidilamrym-ops): static scan clean, 67.2% = truncation of 2 − 1/cMT = 0.672500…, no Lean run | headline covered, decimal certified in Lean, (0,T) **rate sentence of the paper UNCOVERED** (not mentioned by either human audit); our advisory scan first reported two `axiom` lines that are inside a docstring | **system found something the humans did not** (uncovered rate). **Humans were right where the system was wrong**: the axiom hits were a false positive of `scan_escapes.py` (Lean block comments nest; the regex did not) — fixed in this run and re-run: 0 axiom hits |
| T3 | not compared (no review read) | DONE | — |
