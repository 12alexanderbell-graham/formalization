# Run 2026-11-05T2028Z (scheduled)

**THE RESULT:** part 1 (every link machine-checked) by rotation (idle since 1028Z, four runs): the two shrink-only lists of links behind headlines that had no independent machine-checked evidence — 28 source claims whose inline formula or series order had been read once, and 11 formulas, witnesses and printed definitions with no blind second version — are now **empty**. Every transcription and every formula a headline rests on now carries a Lean-checked agreement with a blind second reading (typeset source) or a blind second formulation (name, roles, conventions).

**What can a scientist now trust without checking it themselves, that they could not before?** That the printed formulas the program refutes are the ones the papers print — including the three behind verified findings F1 (Aviles et al. 2012 l₀, m₀), F2 (Capozziello–Lazkoz–Salzano 2011 l₀) and F9 (Bamba et al. 2012 (11.13), (11.21)) — and the order at which each refuted series is claimed: a second reader working only from the typeset pages wrote them independently and Lean proves the two readings equal. And that the corrected F(R) denominator of F9 is not only the program's derivation: a blind formulator re-derived it from the field equations and it agrees term by term.

**Weakest unchecked step:** the second readers and formulators are language models (Sonnet; the first readings were by the main model). Agreement is checked by machine, but two models can share a misreading. The generated claim templates (`Checked/Trust/SecondReadingClaims.lean`) are the program's text with the readers' data substituted: the quantifiers, hypotheses and remainder templates of each claim are covered by its blind restatement (fidelity audit), not by this reading.

## Start
- 20:28Z: no LOCK; pre-cloned checkout on a detached HEAD reset to origin/main (bb14609). LOCK + stub da1be87.
- Local Lean: elan installer accepted; Mathlib cache; full `lake build Checked` started at 20:31Z in the background.
- Bottleneck: part 1 by rotation. Candidates in STATE (FR13 bridge to `IsFlatLCDM`, stiff Robertson network, Moresco four-decimal minimum) against the trust map's own list of links without evidence (`claim_baseline.txt` 28, `formula_baseline.txt` 11). Chosen: the baselines — they are links the system itself declares unchecked, three of them under verified findings already reported to Alexander; a yes empties both lists, a disagreement would be a transcription error inside a reported finding.

## Work
1. **Inventory** (`claim_baseline.txt`, `formula_baseline.txt`): of the 28 CLAIMs, 4 carry genuine inline formulas (Aviles l₀, m₀; CLS l₀; Bamba (11.13)), 2 the normalisation of (11.21), 22 only the order of a printed series (the exponent of the remainder and zero placeholders); of the 11 baselined definitions, 2 PRINTED (`dQFlat`, `jL`), 9 FORMULA/MATH/WITNESS.
2. **Blind second readings** in one message (Sonnet; `second_reading_claims/BRIEF_COMMON.md` + `BRIEF_A.md`, `BRIEF_B.md`, later `BRIEF_C.md`): readers saw only typeset crops and their own renders of arxiv.org/pdf (all versions). They report raw printed data (formula; power of the prefactor; last printed power), not the program's reading. Each took 2–3 min. Side observations, unprompted: reader A found the printed Aviles l₀, m₀ inconsistent with Einstein–de Sitter (F1); reader B found the printed (11.13) nonzero in de Sitter (F9/C11) and that the d_L(y), d_A(y) series are printed only as coefficients (the Underspecified reading recorded for C5).
3. **Generated claims** `scripts/gen_claim_readings.py`: each program claim's text with each source-dependent datum replaced by the reader's constant (every replacement matched once; truncations below the last printed order written `Last − k`). Agreements: 28 by `rfl`, the two (11.21) claims by `simp only [… , neg_one_mul]`. Mutation check: `cvdQ59Last := 3` or `bambaF0Norm := 3` breaks four agreements.
4. **Blind second formulations** (`blind_formulation/briefD.md`, `briefE.md`): D wrote seven definitions in ≈ 3 min, deriving `correctR` from the F(R) field equations with sympy (it equals the program's proposed correction of (11.31) term by term: an independent derivation of F9's correction by a different model); E wrote `margChiSq` with prior s.d. |σ|, which agrees for every σ (the 0828Z formulation only for σ > 0).
5. **Integration**: modules in `Checked/Trust/`, baselines emptied, `scripts/trust/Claims.lean` extended (CLAIMs with a second reading say so), relock (104 new entries, none changed), TRUST_MAP, CLAIMS.md, packet. Commit 48c7e7d.
6. **Audits registered**: the 48 theorems of `Work/Data/FR13Audit.lean`, `Work/Chemistry/RKAcentricAudit.lean`, `Work/Cosmography/B1L19CurvedAudit.lean` added to `scripts/trust/audits.txt` (STATE next step 5 of run 1828Z).

## CI
- Read: 1828Z commits 529cd99, ecf67d2, db8d795, 85ab963 green; **promotion 414e080 42098722467 green on every job** (build 17 min, nanoda 19 min, trust step 7 min): `pr78_omega1_unique`, `pr78_omega1_exists` PROVED.
- bb14609 (1828Z records) 42098780580 green; da1be87 (LOCK) 42103639109 green.
- **48c7e7d (baselines) 42112512656: every blocking step green** (checked: build 15 min, nanoda 18 min, trust step 4 min incl. StatementDeps with both baselines empty, frozen registry; work, packet, goal guard). The 30 claim agreements and 8 formulation agreements are thereby machine-checked in CI.
- dd055a6 (records) 42113143146: **work job green, incl. AuditClosed with the 48 new audit theorems**; checked job in progress at the close. Final commit (LOCK removed): read next run.

## Measurement
| | before | after |
|---|---|---|
| grandfathered links without independent evidence (claim + formula baselines) | 39 | 0 |
| PRINTED definitions with a blind second reading | 42/44 | 44/44 |
| FORMULA/MATH/WITNESS definitions with a blind second formulation | 23/31 | 31/31 |
| CLAIMs whose inline data were read twice | 0/28 | 28/28 |
| disagreements found | — | 0 |
| registered closed audit theorems | 463 | 511 |

- Prepared for part 3: `briefL_addendum.md` (aim round L at this run's evidence route).

## Next step
See STATE.md "Exact next step".
