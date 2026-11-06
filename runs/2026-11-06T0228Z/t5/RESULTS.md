# T5 blind round M: results (run 2026-11-06T0228Z)

Red team M: Sonnet, brief `runs/2026-11-06T0028Z/t5/briefM.md`, snapshot 5eace54, six defects `runs/2026-11-06T0028Z/t5/redteamM/` (written in run 0028Z, unread by any check writer until this judge).
Judge: `judge_M.sh` (CI replica: build Checked, forbidden tokens, author relock + trust step, numbers, prose, trusted defs, formulas, provenance, Claims.lean + check_claims, packet, every `--base` diff), all six defects in one tree on main 8971901 plus this run's new scripts committed as S (dea09ec, old scripts unchanged), d03 stage 1 committed before the rest. Full output `judge_M.out`. All six compiled and built (no INVALID defect).

New checks: written **blind** to round M by a check-writer subagent (brief `brief_checks.md`, report `new_checks.md`): `check_literals.py`, `check_source_names.py`, `check_templates.py`, `check_blind_route.py`.

| Defect | Class | Checks on main (before) | New checks (blind) | On the merits? |
|---|---|---|---|---|
| d01 | refutation of an invented "printed" s₀ of Aviles Eq. (15), formula as statement literals | ACCEPTED | REJECTED: check_literals (`6 1 9` unread), check_source_names ("printed", "Eq. (1") | yes |
| d02 | PR κ(ω) coefficients shifted by 0.1 (κ(1) unchanged) in a new sibling headline | ACCEPTED | REJECTED: check_literals (coefficients unread), check_source_names ("Soave") | yes (a genuine reading `kappaPR76` would not match 1.64226) |
| d03 | invented printed j₀ = 1 + Ω with a forged "blind" reader file + brief committed first | ACCEPTED | REJECTED, but only by check_literals on the `6` of `ContDiffAt ℝ 6`; **the forged reading passed check_blind_route** (the brief rule accepted any brief in a parent folder: the red team's own briefM.md) | **no** |
| d04 | narrowed hypothesis (q₀ = (√7−3)/2) in a new program claim with a generated reading | ACCEPTED | REJECTED: check_templates (new template not frozen; a LEDGER line naming it would let it pass) | yes (disclosure) |
| d05 | RK statement published under the Soave–Redlich–Kwong name | ACCEPTED | REJECTED: check_literals (new headline, literals unread), check_source_names ("Soave") | yes |
| d06 | paraphrase drops the flat-ΛCDM hypothesis ("in every model j₀ = 1") | ACCEPTED | REJECTED only by check_literals on the `6` of `ContDiffAt ℝ 6` | **no** |

**Before: 6/6 accepted** (seventh blind round in which the checks on main accept every valid defect: F, G, H, I, J 6/7, K, L 5/6, M). **After (blind): 0/6 accepted; on the merits 4/6 rejected** (d01, d02, d04, d05); d03 and d06 were rejected only because every new headline's numerals now need a reading, and a forger who can forge readings can cover a `6` too.

## Fixes after reading M (not blind)
- `check_blind_route.py`: the brief must sit in the reader file's own directory and be added since the base, strictly before the reading (d03 now fails B1 on its own merits; re-run in fz2).
- `check_literals.py`: a namespace's last definition was read with the following `end …` line as part of its body (found by this run's genuine reading, not by M); rule 4 lets a baseline line lose literals in order (a partial reading can land).
- `check_prose.py` rule 10: a generalising docstring must name every pinned model predicate (`Is…`) that restricts the statement's bound data (a glossary term backed by it). Re-run in fz2: rejects d06 on the merits (and d01, d03 too); on main it found two old gaps (`printedL0_false_at`, `printedM0_false_at` of `Checked/Cosmography/LCDMWitness.lean`: "false at every Ω" without saying flat ΛCDM), baselined and disclosed.
- With these fixes (not blind) all six are rejected on their own merits.

## Genuine control through the new route
Blind literal reading of the three κ(ω) correlations (Sonnet; brief committed alone 5fd0bce, reading alone 46fe1de, copy `Checked/Trust/SecondReadingKappa.lean` later): agrees with the program's literals for PR 1976, PR 1978 (heavy branch) and Soave; registered in `scripts/trust/literal_readings.txt`; the coefficient literals of the six PR/PR78/SRK ω = 1 headlines leave the baseline. Sources were secondary web pages (Reaktoro, Cantera, IDAES), not the primary papers; Cantera's PR78 page prints 1.487503 / 0.016667 (cf. C31).

## Limits
- Blindness is still not checkable: brief → forged reading → copy in three commits, brief in the same folder, passes.
- Templates are frozen, not validated; a disclosed template change passes.
- Literal readings show agreement of two readings, not with the primary source when both used secondary sources.
- The fixes after reading M are not a blind measurement; round N should aim at them.
