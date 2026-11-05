# Adversary on the five new checks of run 2026-11-05T1428Z (Sonnet, static read of the diff; nothing built)

Brief: break each new rule with a wrong or overstated claim, CI green, no LEDGER line. Report as returned (the subagent's Write was refused; transcribed here by the run, condensed).

| Rule | Bypass | Adversary's confidence | Status after this run |
|---|---|---|---|
| 1 disclosure | second reading in a sub-directory `Checked/Trust/SecondReading/X.lean` (glob not recursive; StatementDeps matches the module prefix) | high | **closed**: every module under `Checked/Trust` whose first path part starts with SecondFormulation/SecondReading/Formulations/Transcriptions, at any depth |
| 1 | re-point an agreement theorem (`Formulations*`/`Transcriptions*` not watched) | medium | **closed**: agreement modules watched too |
| 1 | delete a module; "briefly" satisfies "brief" | medium | **closed**: deleted modules count as changed; `\bbrief\b` |
| 2 COMPOSITE | `scaleBy 36 r` with a listed generic helper (numerals passed to program constants are skipped) | high | **closed**: any non-natural numeral > 1 or decimal anywhere in the body (`realNumeral`) |
| 2 | repetition `g + g + … + g`, `x + 1 + 1` | high | open (no numeral to see) |
| 2 | alias `schwarzschildRadius := gravRadius` (name carries the false factor) | high | open: names of COMPOSITE definitions are unchecked (class J d06) |
| 3 CLAIM | invented formula written directly in the headline statement (no CLAIM definition) | medium | open (headline literals are printed in CLAIMS.md and read by the number rule, but no source check) |
| 3 | `let t := Ω+Ω+Ω; 1 + t + …` (only the literal 1) | high | open |
| 3 | coefficients as helper arguments `quad 1 3 27 Ω` | medium-high | **closed** by `realNumeral` |
| 4 junk | hypothesis not literally `x = 0` (`x ≤ 0 ∧ 0 ≤ x`, `|x| = 0`, aliasing `b = 0`, `a t = b`), ∃ form | high | open (syntactic rule) |
| 4 | other junk values: `Real.log 0`, `x ^ (-1 : ℤ)`, `√` of negatives, junk derivatives | high | `Real.log` **closed**; the others open |
| 5 rule 8 | any unrelated PRINTED definition in the statement satisfies the data rule | medium-high | open (relevance-blind) |
| 5 | vocabulary gaps (observations, CMB, WMAP, DESI, SDSS, SH0ES, posterior, MCMC, chi2, Hubble diagram) | high | **closed** for those words; camel-case names vs multi-word glossary terms open |
| 5 | data claims in module docs, non-headline docstrings, records | medium | open for rule 8 (module docs are frozen; records are labelled unchecked prose) |

Expected false positives named by the adversary: honest COMPOSITEs with −1; honest CLAIMs with small numerals (grandfathered in `claim_baseline.txt`; new ones need a blind second reading); English uses of "fit", "data", "measured", "Planck"; module names with glossary terms (the glossary now reads the headline's own name only).
