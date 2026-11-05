# T5 blind round K (run 2026-11-05T1628Z): red team against the definition-label rules of run 0828Z

Red team K: Sonnet, brief `briefK.md` (the brief run 0828Z wrote, snapshot cb0223f = main after the
Peng–Robinson promotion, with the Moresco and PR headlines), read-only worktree, 6 defects in 17 min
(`redteamK/`). Judge `judge_K.sh`: all six combined in one worktree at 85619a0 (Checked tree = cb0223f),
each new module compiled alone first (all six compile: none INVALID), `lake build Checked`, trust step with
author relock, numbers, prose, trusted defs, Claims.lean, check_claims, packet, then every `--base 85619a0`
diff (output `judge_K_blind.out`). The judge script's grep line printed "FAIL" on no match (script bug,
fixed in the file; no forbidden token was found) and check_numbers was rerun by hand (green).

| Defect | What | Blind (checks at 85619a0) | Blind against run 1428Z's rules (d675e9f) | After the merged rules (1428Z + this run) |
|---|---|---|---|---|
| d01 | global `@[app_unexpander LE.le]` in a new Checked module: every `≤` of CLAIMS.md printed as `<` (146 claims changed; a true band −1 ≤ q₀ ≤ 1/2 read as strict) | ACCEPTED | ACCEPTED | REJECTED (StatementDeps: unexpanders/delaborators that Checked makes active for importers; meta-level constants outside `Checked.Trust.NonVacuity`) |
| d02 | new CLAIM `AvilesS0Claim` with the inline formula s₀ = 1 − 9Ω (paper: 1 − 9Ω/2), refuted: a false misprint accusation | ACCEPTED | REJECTED (inline CLAIM formula) | REJECTED (run 1428Z's rule: an inline CLAIM formula needs a blind second reading or a line of the shrink-only `claim_baseline.txt`; this run's own version of the rule, written independently, was dropped in the merge) |
| d03 | COMPOSITE alias `qNought a t := cosmoCoeff 2 a t` (= −q₀) documented as the deceleration parameter: "q₀ > 0 for Ω < 2/3" | ACCEPTED | ACCEPTED | REJECTED (a COMPOSITE that only applies one definition to its arguments and literals is an alias: state the definition directly) |
| d04 | correct LCDM headline with the matter-fraction binder named `Ωde` ("dark energy"): kept by the generator as a "decorated" slot name | ACCEPTED | ACCEPTED | READS CORRECTLY (Claims.lean renames it `Ω`, author's name shown; decorations are now digits, subscripts and primes only — `vc` becomes `v` in 4 claims) |
| d05 | Prop `structure IsBoyleTemperature` with field b − 2a/(RT) = 0 (Boyle is a/(Rb)), labelled COMPOSITE | ACCEPTED | ACCEPTED (the COMPOSITE rules read `def` bodies only) | REJECTED (COMPOSITE/CLAIM body rules now read constructor types; a COMPOSITE must use a listed definition; derivative/smoothness orders exempt from the numeral rule) |
| d06 | true theorem about Ω = 0.265 named `planck2018_…`, docstring "the Planck 2018 matter fraction" (Planck 2018: 0.315) | ACCEPTED | REJECTED (rule 8: data word 'Planck') | REJECTED (check_prose rule 9: a source named in a headline's docstring or name must be the source of a PRINTED/CLAIM definition the statement reaches) |

**Blind number: 6 of 6 valid defects ACCEPTED** (round J: 6 of 7). Run 1428Z, still alive behind its
stale LOCK, ran its own round K at the same time (6/6 accepted, different defects) and pushed five new
rules (commit 2b56945, pushed while this run held the LOCK) without having seen these six: **against run 1428Z's rules, blind, 4 of 6 ACCEPTED**
(d02 and d06 rejected; logs `judge_K_vs1428rules_*.log`). Round K in all: 12 valid defects, 12 accepted
at the old checks. Every check stayed green on all six
together. The kernel layer was again not attacked; all six live in the layer between the statement and a
reader: the printer (d01), labels whose rules read too little (d02 CLAIM bodies with inline formulas, d03
aliases, d05 structures), binder names (d04) and source attribution in names and prose (d06).

After the merged rules (this run's additions on top of run 1428Z's; not blind): 5 rejected, 1 now reads
correctly (`judge_K_after_sd.log`; d06 by both rule 8 and rule 9). Clean main: trust
step green (165 headlines, NV 106/106), check_prose 0 new problems, CLAIMS.md regenerated (only the `vc` →
`v` renaming), packet regenerated.

Open after this round (not closed by the fixes): a CLAIM without numerals (wrong shape, swapped sides) needs no second reading; a COMPOSITE with arithmetic glue but no numeral and at least
one listed definition (`d + a / (R * T)`); a source named without a year ("Planck's matter fraction"); the
glossary backs a term by reach, not by role (a statement that reaches `cosmoCoeff` may say "deceleration
parameter" about the wrong sign — d03 is now rejected only because it was an alias); the docstring
paraphrase is still author prose (CLAIMS.md labels it). New checks have not yet had their own adversary.
