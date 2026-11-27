# Run 2026-11-27T1028Z

**THE RESULT:** part 3 (what a reader may rely on without trusting the authors): the last three pinned definitions with no blind specification reading (the expansion-rate equation, the second field equation and the dust density of F(R) cosmology in Bamba et al. 2012 §XI) read by three sourced blind readers (Sonnet, Opus, Haiku); all nine readings closed in Lean against the program's definitions, in `Checked` and on the claims page. Every pinned definition now has at least one independent reading it meets. Also: the two junk-value disagreements of run 0228Z (the chemistry conditions on derivatives and on an integral) shown in Lean to reach no state the chemistry headlines speak of.

**What can a scientist now trust without checking it themselves, that they could not before?** That the program's F(R) field equations and dust density are what three independent readers of the source's LaTeX take them to be (section What we did; `Checked/Trust/SpecAgreementIJK.lean`, standard axioms); that the source's minus sign of the Ricci scalar, which all three readers flagged, is one consistent convention (the program's equations are the textbook ones for the Lagrangian with both signs flipped, proved for every scale factor and Lagrangian); and that the chemistry conditions do not rest on Lean's junk derivative or junk integral at any isotherm state above the co-volume (`Checked/Trust/JunkImmaterial.lean`).

**Weakest unchecked step:** the readers are subagents of the author's model family, briefed by the author; blindness is checked only structurally (`check_blind_route`). The source excerpt is a transcription by the orchestrator (verbatim lines with the e-print's hash): no reader saw the typeset PDF.

## Start
- 10:27Z. Session clone detached; `git checkout -B main origin/main` (9f275ee); `scripts/start_run.sh` (elan 4.35.0, Mathlib cache, commit-msg hook).
- **`LOCK` held by run 2026-11-27T0828Z** (started 08:28Z, heartbeat 10:01Z, 26 min old; task: H₂⁺ angular certificate, then records): alive, so this run takes the auditor role (48.4): writes only in `runs/2026-11-27T1028Z/` and appends to `CHANGELOG.md`; no `STATE.md`, `Checked/`, `scripts/` until the LOCK is free.
- **`EXTERNAL_LOCK` held by run 2026-11-27T0628Z** (heartbeat 10:22Z, 5 min old; targets R and O): the external targets stay with it (PROMPT 11).
- Env: repo ok (`add_repo` not exposed in this session; the clone was present, push works). Local Lean 4.35.0 with the Mathlib cache; `lake build Checked.Cosmography.FRCosmo` started for the closures.

## Bottleneck
Section Next (b) of `runs/2026-11-27T0228Z/README.md` (part 3): 71 of the 494 pinned definition uses on the claims page rest on a specification only the program wrote: `FRCosmo.FriedmannEq`, `FRCosmo.MasterEq`, `FRCosmo.rhoM`. They are disjoint from both live runs' tasks. Yes (sourced readers' specifications are met by and determine the definitions) → those uses gain a blind reading; no → the definition differs from an independent reading of its own source, proved, and the page must show it.

## What we did
- Sources (`sources/`, outside the readers' folders, B5): `bamba2012_1205.3421v3.md`, a byte-identical copy of run 0428Z's verbatim LaTeX excerpt of arXiv 1205.3421v3 (§II metric, §VIII.C, §X, §XI through (11.6); e-print sha256 in its header).
- Briefs `specI/briefI.md` (Sonnet), `specJ/briefJ.md` (Opus), `specK/briefK.md` (Haiku): three items each, quantity + source + Lean type, never the formula; committed before the readers run (83e7b55).
- Readings committed alone (4f5370e), replies transcribed (`spec*/reply*.md`). All three compiled first time; reader J wrote every formula inline (no helpers), K added smoothness side conditions.
- Closure (`agreement/theorems.lean`, generated file `agreement/SpecAgreementIJK.lean` by `agreement/mk_agreement.py`, 0e033ff): 

| definition | I (Sonnet) | J (Opus) | K (Haiku) |
|---|---|---|---|
| `rhoM` | AGREES (a(t₀), a(t) > 0) | AGREES (a(t₀), a(t) ≠ 0) | AGREES (> 0, a differentiable at t₀) |
| `FriedmannEq` | AGREES (a > 0, F′(R) ≠ 0) | AGREES (a ≠ 0, F′(R) ≠ 0) | AGREES (+ a C³ near t, F C² at R) |
| `MasterEq` | AGREES (a > 0, F′(R) ≠ 0) | AGREES (a ≠ 0, F′(R) ≠ 0) | AGREES (+ a C⁴ near t, F C³ near R) |

  Every reader generalised the source's `a⁻³` (written for a₀ = 1) to (a(t₀)/a(t))³, as the program does; every reader used §XI's `R = −6(Ḣ + 2H²)` and flagged it as opposite to §VIII.C and to the usual sign; J flagged the `+ +` of the printed master equation (a commented-out line break) and asked whether §XI mixes conventions.
- **The convention question settled in Lean** (`friedmannEq_iff_standard`, `masterEq_iff_standard`): with f(x) = −F(−x) and Rₛ = 6(Ḣ + 2H²), the program's §XI equations are exactly 3f′H² = ρ + (Rₛf′ − f)/2 − 3HṘₛf″ and −2f′Ḣ = ρ + R̈ₛf″ + Ṙₛ(Ṙₛf‴ − Hf″), for every a and F, no smoothness assumed (Mathlib's derivative of a composition with negation needs none). Flipping the signs of R and of the Lagrangian together is a convention; F(R) = R is general relativity in both.
- **LOCK released by run 0828Z at 10:38Z (868eee2); taken 10:45Z (59f0eff).** Copy steps done in this run: `Checked/Trust/SecondReadingSpec{I,J,K}.lean` (code unchanged, provenance header), `Checked/Trust/SpecAgreementIJK.lean` (theorem part with the imports), `Checked.lean`, `scripts/trust/Claims.lean` (`blindSpecNote` reads readers I, J, K, marked sourced).
- **Part 3 (d) of run 0228Z's Next, decided without a definition change** (`Checked/Trust/JunkImmaterial.lean`, drafted in `junk/`): for `cubicP R a b u w T` with b > 0, u > −2, 1 + u + w > 0 (vdW, RK, SRK, PR 1976 and 1978), the isotherm and its derivative are differentiable at every volume above b and the isotherm is integrable on every interval above b; hence readers E's and F's critical-point and coexistence specifications are equivalent to the program's conditions there (`critical_agrees_E/F`, `coexistence_agrees_E/F`), and every program coexistence state with liquid volume above b meets the readers' (`coexistence_agrees_of_liquid_E/F`). Every chemistry headline quantifies only over such states (`b < v`, `b < vl`), so the junk admissions do not reach any of them; changing the definitions would cost a relock and every chemistry headline for no change in meaning. Not yet on the claims page (next).

## Measure
- Pinned definitions with a blind specification reading: 20 of 23 → 23 of 23; pinned definition uses on the claims page determined by an agreeing blind reading: 423 → 471 of 494 (the other 23 are uses of the critical-point and equal-area conditions, where readers E and F disagree only through junk values; `JunkImmaterial` proves that immaterial on every headline state, which the page does not show yet).
- Blind specification readings: 48 → 57 (9 new, 9 agree); sourced readings 8 → 17.
- Junk-value disagreements shown to reach a headline's states: 2 open → 0 (both proved immaterial for every cubic-EOS state above the co-volume).

## Next
- **CI read first:** the run of this run's final push (new `Checked/Trust` modules `SecondReadingSpec{I,J,K}`, `SpecAgreementIJK`, `JunkImmaterial`; `Claims.lean` reader list; relock, pages regenerated). Green on every job → nothing to promote (no headline changed). Red → its first failing command, base 5c678d6 (45956936101, green on every job) or the newest fully green descendant.
- Part 3 next: (a) show `JunkImmaterial` on the claims page next to readers E's and F's DISAGREES on `IsCriticalIsotherm` and `IsMaxwellCoexistence` ("the disagreement does not reach a cubic isotherm above the co-volume", with the theorem names), e.g. a `materialNote` in `Claims.lean` keyed on `*_agrees_*` theorems naming the definition; likewise for reader F's empty-interval disagreement on the three ODE solution predicates (every simulator headline has a positive final time: prove it the same way); (b) the remaining memory-only readings (A–F) re-read with the source, starting with the links whose agreement rests on a convention (`curvK`, the order-2 coefficient's sign); (c) as in run 0228Z's Next, compare each pair of pins' domains mechanically.
- Part 1 next: as in section Next of `runs/2026-11-27T0028Z/README.md`. Parts 2/5 next: as in section Next of `runs/2026-11-27T0828Z/README.md`.
- External test: while `EXTERNAL_LOCK` is fresh, run 0628Z keeps it.

## End
- Local: `lake build Checked` (3867 jobs, no error) with the judge's build of 5c678d6 restored; `#print axioms` on all 20 theorems of `SpecAgreementIJK` and the four `*_agrees_*` of `JunkImmaterial` (propext, Classical.choice, Quot.sound); no `sorry`/`axiom`/`native_decide`; `precheck_names` ok; `check_prose` 0 new (after replacing the arXiv identifier in the copies' module docs by words; code unchanged, `check_provenance` ok); StatementDeps relock (316 headlines, open 14); Claims (316; 471/494 pinned uses with an agreeing blind specification); `make_packet.py`, `check_numbers.py --write`, `make_verified_page.py`; `records_check.py 5c678d6` (rerun after the record rewording: `check_headline_mentions` 0 findings).
- CI: run 45984094021 (868eee2, run 0828Z's final push) in progress when read. This run's final push 5ee415b: Lean judge run **45992056288** (queued at 11:38Z behind it); the next run reads it first (section Next).
- Message to Alexander (L.2): none (no headline or status changed; no verified finding; the external test's messages are run 0628Z's).
