# Run 2026-11-05T1428Z (scheduled)

**THE RESULT:** part 3 (measured trust) by rotation (idle since 0828Z): blind red-team round K against the definition-label rules of run 0828Z — **6 of 6 valid wrong claims accepted by every check on main**; five new blocking rules written after reading them reject all six; an adversary on the new rules found further bypasses, the high-confidence ones of rules 1–3 closed the same run.

**What can a scientist now trust without checking it themselves, that they could not before?** That a definition shown in CLAIMS.md as agreeing with a "blind second formulation" or "second reading" had that independent version disclosed in LEDGER with its brief (any declaration, any changed or moved agreement module — K's d01/d03 slipped a self-written one past the `def`-only pattern); that a COMPOSITE contains no hidden constant and really combines listed definitions; that a CLAIM attributed to a source with an inline formula has been read twice or is one of 28 listed grandfathered claims; that no headline's conclusion rests on dividing by (or taking the log of) a quantity it assumes zero; and that a headline whose name or docstring speaks of fits or data reaches a transcribed table.

**Weakest unchecked step:** blindness of the "blind" second formulations and readings themselves — machine-checked agreement, but who wrote the independent version is only disclosed (LEDGER), not checked. Next: the alias/name class (a COMPOSITE named as physics) and non-literal junk hypotheses (`adversary_new_checks.md`).

**Kind of result:** measurement (false-acceptance rate, blind: 6/6) plus strengthening (after: 0/6, not blind; a later blind round must measure the new rules).

## Start
- 14:28Z: no LOCK; add_repo not exposed; pre-cloned detached HEAD, stale local main reset to origin/main (46a759e). LOCK + this stub 01b0c8c.
- Local Lean: elan installer accepted, Mathlib cache; full `lake build Checked` uncached 14:45–16:16 (≈ 90 min, slower than the 55 min of run 1228Z: the curved B1 and Moresco certificate modules ran in parallel with the red team's reading and the judge preparation).
- CI: promotion 6a32db1 **42039795953 green on every job** (checked build 17 min, nanoda 19.5 min, trust step 5.4 min) ⇒ `pr_omega1_unique`, `pr_omega1_exists` **PROVED**. Records 46a759e 42040438574 green. LOCK commit 01b0c8c 42045496695: checked job lost 1.5 min into the build (runner loss; read by run 1628Z in auditor role, which pushed cb0223f while this run held the LOCK).

## Work
1. **Blind red team K** (Sonnet; brief `t5/briefK_used.md`, read-only snapshot 01b0c8c; ≈ 15 min): six defects, all new headlines in new files (`t5/redteamK/`).
2. **Judge** (`t5/judge_K.sh`, worktree at 01b0c8c, all six combined, full Checked build, author relock, every CI check and `--base` diff): **before: 6/6 ACCEPTED** (`t5/judge_before.txt`).
3. **Five rules** (LEDGER): disclosure of second formulations/readings and agreement modules at module level (`check_formulas.py`); COMPOSITE without constants and with a listed definition; CLAIM inline formulas need a second reading or `claim_baseline.txt` (28 grandfathered); junk-value rule (zero hypothesis divided by or logged); `check_prose.py` rule 8 (glossary on names, data words need a PRINTED definition).
4. **Adversary on the new rules** (Sonnet, static; `t5/adversary_new_checks.md`): bypasses of rules 1–3 rated high closed (recursive module watch, agreements, deletions; `realNumeral` for helper arguments); the rest recorded as open.
5. **Judge after: 0/6 accepted** (`t5/judge_after.txt`; d01/d03 by `check_formulas --base`, d02/d04/d06 by StatementDeps, d05 by check_prose). Main: StatementDeps green with the new rules (165 headlines), check_prose 0 new (4 old gaps found by rule 8, baselined and disclosed), check_claims, check_numbers, packet green; TRUST_MAP.md and CLAIMS.md unchanged.

## Measurement
| | before | after |
|---|---|---|
| Blind round K, valid defects accepted | 6/6 (checks at 01b0c8c) | 0/6 (new rules, not blind) |
| Definition labels whose evidence is disclosure-checked at module level | SecondFormulation `def`s only | every declaration and module of SecondFormulation, SecondReading, Formulations, Transcriptions |
| CLAIMs with an inline formula and no second reading, unlisted | 28 (unchecked) | 0 (28 in a shrink-only baseline) |
| Junk-value headlines (zero hypothesis divided by) on main | not checked | 0 (checked, blocking) |

## Concurrency
- The full local Checked build took 90 min, so nothing was pushed between the LOCK commit and 16:58Z; run 1628Z took over the LOCK as stale (48.4) at 16:58Z and started its own red team K against cb0223f (same checks as 01b0c8c). This run pushed its rules afterwards as one commit (2b56945; scripts, LEDGER entry, run folder; no Checked change) and these records (append-only; STATE.md left to the LOCK holder). Run 1628Z's defects, written without seeing the new rules, are a blind test set for them (LEDGER).

## Trust-track line for STATE
- **T5 blind round K (run 2026-11-05T1428Z; `runs/2026-11-05T1428Z/t5/RESULTS.md`; LEDGER; blocking):** red team K (Sonnet, six new headlines against 01b0c8c): **6/6 ACCEPTED** — self-written "blind" second formulation as `abbrev` (d01) and second reading (d03), a free formula labelled COMPOSITE with 6 spelt 1+…+1 (d02), pinned `redshift` at a(t) = 0 (x/0 junk, d04), a data claim carried by name/docstring (d05), an invented formula attributed to a real paper as a CLAIM (d06). New rules: module-level disclosure of second formulations/readings and agreements (`check_formulas.py --base`); COMPOSITE without constants and with a listed definition; CLAIM inline formulas need a second reading or `scripts/trust/claim_baseline.txt` (28, shrink-only); zero hypothesis divided by or logged is rejected; `check_prose.py` rule 8 (glossary on names; data words need a PRINTED definition). After: 0/6 (not blind). Open: repetition constants, aliases named as physics, non-literal zero hypotheses, other junk values, relevance-blind data rule; blindness of second versions is disclosed, not checked.

## Next step (for STATE; not written into STATE.md because run 1628Z held the LOCK when this run pushed)
0. **Read PROMPT instruction 10 and `TARGETS.md` "THE RESULT" first.** Part rotation: part 3 at 1428Z (round K), part 5 at 1228Z (PR), parts 1 and 2 at 1028Z (idle two runs), part 4 waits on Alexander. Next run by consequence: part 1 or 2 (new science through the system), or a blind round L against this run's rules if a fresh snapshot is cheap.
1. **Read CI** of this run's commits (rules + records): the new StatementDeps rules and `claim_baseline.txt` must be green on main (locally: StatementDeps green, 165 headlines; check_prose 0 new; check_formulas, check_claims, packet green). If a checked job is lost again (three runner losses today, all no-log): add swap before the build/nanoda step in `.github/workflows/lean.yml` (repair, annex LIV) and record the experiment.
2. **Part 3 follow-ups** (`runs/2026-11-05T1428Z/t5/adversary_new_checks.md`, open column): aliases and repetition in COMPOSITE bodies (idea: a COMPOSITE's name must not carry a glossary term its body's definitions do not reach; or require a second formulation for every COMPOSITE whose name is not derived from its parts); zero hypotheses in other forms (decide `x = 0` through `simp`-normal forms of the hypotheses); other junk values (`x ^ (-n : ℤ)`, `Real.sqrt` of negatives, `deriv` of non-differentiable functions); relevance of the PRINTED definition in rule 8. Then blind round L (brief: copy `briefK.md`, aim at these rules). Shrink `claim_baseline.txt` (second readings of the Aviles/CLS/CVdQ claims from the typeset crops in `runs/`) and `formula_baseline.txt`.
3. Part 5 follow-ups: PR 1978 κ at ω = 1 (the referee's floats: ω_out = 1.0001; the generators take a new κ by changing one constant); SRK with Soave's κ; the κ coefficients of PR 1976 from a typeset source; Lane–Emden n = 3/2, Bonnor–Ebert constants.
4. Part 2 candidates (answers not in print): four-decimal enclosure of the Moresco minimum (737 boxes); certified global minima of other published fits.
5. Register `Work.Data.FR13Audit.*`, `Work.Chemistry.RKAcentricAudit.*`, `Work.Cosmography.B1L19CurvedAudit.*` in `scripts/trust/audits.txt` (`AUDIT_WRITE=1` with a full Work build).
