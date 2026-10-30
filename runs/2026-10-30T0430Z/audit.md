# Fidelity audit: C4, flat matter + CPL cosmographic coefficients (Capozziello, Lazkoz, Salzano 2011, Eq. (22))

Promoted: `Checked/Cosmography/CPLCoefficients.lean`, namespace `Checked.Cosmography.CPL`.
Frozen in commit `4663ac9` (`Work/Cosmography/CPLCoefficients.lean`), before any proof. Statements
unchanged since (`git diff 4663ac9` removes only `sorry`s; one helper lemma `cplW_law` and a
`set_option maxHeartbeats` line added). Work and Checked differ only in namespace and module
docstring (checked by `diff`).

Headline declarations: `IsFlatCPL` (definition; reuses audited `cosmoCoeff`, `hubble`, `redshift`,
`decel`); `CLSL0Claim` (frozen printed claim); `flatCPL_coeffs` (correct q₀, j₀, s₀, l₀ for every
Ω, w₀, wₐ); `printedL0_ne` (printed l₀ false in every model with (1−Ω)(7−Ω)wₐ ≠ 0);
`clsL0Claim_false` (refutation by explicit model); `cplW`, `cplW_isFlatCPL` (witness).

**SOURCE.** S. Capozziello, R. Lazkoz, V. Salzano, PRD 84, 124061 (2011), arXiv:1104.3096 v1 and v2,
Eqs. (2), (16), (17), (19)–(22), p. 3–4. Typeset text: rendered PDF pages, both versions
(`runs/2026-10-30T0220Z/typeset/C4_cls2011_eq19_22_v*.png`, `typeset/crop_v*p4-04.png`) and the PDF
text layer. Quotes: `source_C4.md`.

**Plain words.** In a flat universe with matter and CPL dark energy, the fifth derivative of the
scale factor today (l₀) is fixed by Ω_m, w₀, wₐ. The paper prints the wₐ² term as
(1−Ω_m)(7−Ω_m)wₐ²/4; the model gives 9(1−Ω_m)(7−Ω_m)wₐ²/4 (a missing factor 9). Every other term,
and q₀, j₀, are right; s₀ is right once the missing "−" operator before 27/4 is supplied.

## 40.2 Blind restatement
Subagent given only `source_C4.md`; no access to Work/Checked/runs/git. Its file: `C4_blind.lean`.
- Same: H = ȧ/a, z = a(t₀)/a(t) − 1, l = a⁽⁵⁾/(aH⁵), H₀ := H(t₀) > 0, Ω_X = 1 − Ω_m, real power,
  no range restriction on Ω, w₀, wₐ, no normalisation of a(t₀).
- Divergences: it imposes Eq. (17) in squared form H² = H₀²E² on an open interval and assumes
  C⁵ on that interval; ours imposes H = H₀√E² eventually near t₀ and C⁵ only at t₀.
  Classified **Underspecified** (the source gives E², not E; smoothness domain unstated).
  Ours is weaker in every hypothesis.
- Closed in Lean (`Work/Cosmography/CPLAudit.lean`, blind block copied verbatim):
  `C4Audit.blind_implies` (blind model ⇒ ours), `blind_l0` (corrected l₀ in the blind model),
  `blind_vs_printed` (printed − true = −2(1−Ω)(7−Ω)wₐ²), `cplW_blind`, `blindL0Claim_false`
  (the restater's own reading of Eq. (22) is false). Local build; CI on the audit commit.
- Restater's independent sympy (`C4_blind_sympy.py`, x = 1+z route) and an mpmath ODE
  integration + finite differences at two interior parameter points agree with our l₀, not the
  printed one. Same model family: shared blind spots possible (40.2).

## 40.3 Sanity tests
- Not vacuous: `cplW_isFlatCPL` (Ω = 0, w₀ = −1, wₐ = 2/3; a(t) = 1 − log(1 − t), analytic near 0);
  `C4Audit.eds_isFlatCPL` (Ω = 1, **every** w₀, wₐ; a = t^{2/3}); `C4Audit.lcdm_isFlatCPL`
  (every flat ΛCDM model is CPL with w₀ = −1, wₐ = 0).
- Bites on examples: `cpl_agrees_lcdm` — on ΛCDM, `flatCPL_coeffs` returns the separately
  generated and proved ΛCDM l₀ = 1 + 3Ω + 27Ω²/2 (F1 theorem); `eds_cpl_consistent` — at Ω = 1 it
  returns 35/2, matching the independent Pochhammer computation `l0_eds`. Witness: l₀ = 24 by hand
  (a⁽ⁿ⁾(0) = (n−1)!, H₀ = a₀ = 1), printed 160/9.
- Not trivial: two coupled eventually-zero polynomial identities (squared Friedmann law; chain
  rule for the dark-energy factor g = (1+z)^{3(1+w₀+wₐ)}e^{−3wₐz/(1+z)}), differentiated 4 and 3
  times, solved at t₀ for a⁽²⁾…a⁽⁵⁾, g⁽¹⁾…g⁽⁴⁾ (sympy-generated certificates, `scripts/gen_cpl.py`).
- Near-miss: `printedL0_ne` — any model with (1−Ω)(7−Ω)wₐ ≠ 0 refutes the printed l₀; at wₐ = 0 or
  Ω = 1 the printed and true l₀ coincide (so the refutation needs wₐ ≠ 0, as it should).
  Dropping H₀ > 0 not tested in Lean (contracting branch flips odd coefficients; recorded).
- Junk values: base of the real power is a₀/a > 0 near t₀; division by a, a₀, 1+z only where
  positive; √ argument shown positive near t₀ (equals 1 at t₀) before squaring; `iteratedDeriv`
  genuine under `ContDiffAt ℝ 5 a t₀`; log in the witness only at 1 − t > 0. No ℕ subtraction,
  sSup, or junk limits.
- Types/quantifiers: real scale factor, two-sided neighbourhood; claim quantified over all
  parameters and models, as Eq. (22) is stated for the model in general.
- Independent derivations of the true l₀: main session (d/dt = aH d/da, `scripts/truth.py`), Lean
  generator (system solve), blind restater (x = 1+z route + numeric ODE), referee (two routes,
  including the paper's own Eqs. (12)–(15)). All agree.

## Classification
**Source** error (misprint) in Eq. (22); Eq. (21) has a missing "−" operator (typographic).
No Translation error found.

## Referee (independent subagent): STANDS-WITH-CORRECTIONS
- Paper's own Fig. 2 (DDE toy model Ω_m = 0.245, w₀ = −0.93, wₐ = −0.41) follows the **correct**
  l₀ (0.809; printed gives −0.906): residual curves recomputed, crossing of the 3- and 4-parameter
  curves at z ≈ 1.35 (correct) vs 1.07 (printed); the published figure crosses at ≈ 1.35
  (`typeset/fig2top.png`, read in main session). Section VI (CPL inversion, Models I–IV) uses only
  Eqs. (19)–(21). So the paper's numbers and conclusions are unaffected.
- Propagation: Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012),
  arXiv:1205.3421, Eq. (11.38) reprints l₀ with the same missing 9 (rendered page, read in main
  session: `typeset/bamba_crop2.png`); its Eq. (11.37) has the s₀ minus restored. That review is
  widely cited.
- Errata: none found (arXiv v1, v2 only; web search). Nobody found pointing out the error.
- Corrections adopted: "missing minus operator" wording for s₀; Ω = 0 witness is a boundary case,
  other Ω covered by `printedL0_ne` (unconditional statement; existence of models with
  0 < Ω < 1, w ≠ const not yet constructed in Lean — next step).

## Addendum: existence for every parameter point (`Checked/Cosmography/CPLExistence.lean`)
Closes the referee's caveat. Headlines: `exists_flatCPL` (for every Ω, w₀, wₐ there is a scale
factor with `IsFlatCPL Ω w₀ wₐ a 0` and `ContDiffAt ℝ 5 a 0`) and `printedL0_false_at` (for every
Ω, w₀, wₐ with (1−Ω)(7−Ω)wₐ ≠ 0, such a model has l₀ ≠ printed). Tool: `exists_local_model`
(any law H/H₀ = E(a/a₀) with E C⁵ at 1, E(1) = 1 has a positive C⁵ solution near t₀ = 0, a(0) = 1),
from Mathlib's `ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀`
(Picard–Lindelöf) and a C⁰→C⁵ bootstrap on an open interval (`contDiffOn_succ_iff_deriv_of_isOpen`).
- Fidelity: reuses the audited `IsFlatCPL`, `cosmoCoeff`; t₀ = 0 and a(t₀) = 1 are normalisations
  (the claim is ∃, so fixing them only makes the witness more specific). `cplE` is Eq. (17) with
  1 + z = 1/x, matched to `IsFlatCPL` inside the proof (no separate trust).
- Not vacuous / not trivial: content is the ODE existence theorem plus the bootstrap.
- Junk values: `1/x`, real power and √ are only evaluated near x = 1 (argument 1 at x = 1);
  positivity of a near 0 is proved, not assumed.
- Consequence: the printed l₀ is false at the paper's own toy-model point (Ω_m, w₀, wₐ) =
  (0.245, −0.93, −0.41) and at every interior point with wₐ ≠ 0. Local build; axioms
  propext, Classical.choice, Quot.sound.
