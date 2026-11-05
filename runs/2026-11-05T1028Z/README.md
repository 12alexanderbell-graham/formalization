# Run 2026-11-05T1028Z (scheduled)

**THE RESULT:** part 1 (every link machine-checked; data claims) and part 2 (certified new science): the Moresco et al. 2016 data claims and the certified minimum of their open-universe χ² — the first certified number in this program that nobody had computed — moved from Work to Checked, on a table read twice independently and on fit statistics whose names a blind second formulation confirms.

**What can a scientist now trust without checking it themselves, that they could not before?** That the smallest χ² any parameter values give for the Moresco et al. 2016 open-universe fit (thirty cosmic-chronometer points, with their H₀ prior) is 14.967 to three decimals — proved over the whole parameter region in `Checked/Data/Moresco16Min.lean`, so that the printed oΛCDM AICc 21.41 is unattainable under the corrected-AIC reading — and that the table and χ² it is about are the paper's: the table agrees entry by entry with an independent second reading, and `e2OL`, `chiSqOL`, `chiSqLine` equal the definitions a blind subagent wrote from their names and the paper's conventions alone. Also, across the whole repository, CLAIMS.md now tells the reader when a printed transcription has been independently read twice (278 of 289 mentions).

**Weakest unchecked step:** the provenance of the second reading of Table 4 (the blind restater of run 0428Z read the paper's pdftotext output; who read what is disclosed in LEDGER, not machine-checked), and the decimal constants 73 and 2.4 of the H₀ prior, which both formulations took from the brief (CLAIMS.md flags them). CI of the promotion was still running at the end of the run.

## Start
- 10:28Z: LOCK of run 0828Z (08:28Z, < 150 min) → auditor role (48.4). Read the probe `probe/kernel-decide` 618f165 (CI 41992993500): the trust step's only errors were missing frozen entries for the probe's own docstrings (no relock on the branch); the summary line before them was green. With nanoda and the axiom audit green in 41987045654, `decide +kernel` certificates pass the checked job once relocked.
- Blind second formulation M launched in auditor role (writes only in this run's folder): Sonnet, brief `blind/briefM.md` (names, argument roles, the paper's conventions, the second-reading table; never the program's bodies) → `blind/SecondFormulationM16.lean` in 30 s.
- 10:39Z: run 0828Z released the lock (d4d1dd8); LOCK + stub 063d3b0.
- add_repo not exposed; pre-cloned detached HEAD, stale local main reset to origin/main. Local Lean: elan + Mathlib cache.

## Work
1. **Promotion by script** (`scripts/promote_m16.py`): ten Work modules copied to `Checked/Data/` with namespaces renamed and `import Mathlib` replaced by specific modules; statements and proofs unchanged. The 905-box cover compiles in Checked in ≈ 11 min (four certificate modules ≈ 2–3 min each), oleans ≈ 30 MB in all; axioms standard.
2. **Labels with evidence** (rules of run 0828Z): `m16Table` PRINTED with second reading (`Checked/Trust/SecondReadingM16.lean`, `TranscriptionsM16.lean`); `e2OL`, `chiSqOL`, `chiSqLine` FORMULA with blind second formulations (`SecondFormulationM16.lean`, `FormulationsM16.lean`): all three agree.
3. **Prose** (`scripts/moddocs_m16.py` and docstring edits): module docs without numbers that are not headline literals (rule 7); headline docstrings without glossary terms that no pinned definition gives meaning (ΛCDM, redshift), quantifier words only over bound variables (rule 6), no unregistered citations. First pass: 10 problems, second: 0. Claims unchanged.
4. **Registration:** 10 headlines, 4 definitions, 5 NV witnesses, relock, TRUST_MAP (163 headlines, NV 104/104, second formulations 23/31), CLAIMS.md, packet.
5. **Audit:** `Work/Data/Moresco16PromotionAudit.lean` — Work definitions are definitionally the Checked ones; the blind restatement of run 0628Z is closed from the Checked headline (audits.txt).
6. **Generator repair** (LIV): CLAIMS.md did not mention second readings of PRINTED definitions; now it does (270/289).

## CI
- Promotion 1783fe6: see below (in progress at the time of writing).

## Measurement
| | before | after |
|---|---|---|
| headlines | 153 | 163 |
| conditional headlines witnessed | 99/99 | 104/104 |
| FORMULA/MATH/WITNESS with blind second formulation | 20/28 | 23/31 |
| PRINTED mentions in CLAIMS.md that disclose a second reading | 0/… | 278/289 |
| formula baseline (shrink-only) | 11 | 10 (`fr13Table` second reading moved to Checked, after the records commit) |
