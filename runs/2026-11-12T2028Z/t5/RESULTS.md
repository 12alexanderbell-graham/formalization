# Blind red team AI — the verified-findings layer (run 2026-11-12T2028Z): results

Red team: Sonnet, blind, brief `briefAI.md` (committed first, 7ad53ed), snapshot 7ad53ed read-only, output verbatim in
`redteamAI/` (committed before judging, 4620626). The red team took 6 min and wrote six defects. All six edit only the
verified-findings section of FINDINGS.md: no Lean, no LEDGER line. Its reason: new Lean would have to pass the
witness, necessity and literal-reading checks, but FINDINGS prose outside the generated blocks was free.

Judge: `judge_ai.sh` runs every Python command of CI's trust step and frozen step (read from `lean.yml`), plus
`goal_guard.py` and `make_packet.py --check`. It runs them on a tree where the author regenerated the certified
blocks (`check_numbers.py --write`) and the packet. Lean outputs come from one local `StatementDeps` + `Claims` run
on the restored CI build of 6a660ac plus run 1828Z's modules, incrementally built. Since no defect touches Lean,
they are identical for every defect. BASE = the snapshot.

## BEFORE (checks of 7ad53ed)

| d | defect | valid? | BEFORE |
|---|---|---|---|
| d01 | F13: Salama 2004's printed 0.005226 changed to 0.005218, which is the correct rounding of the certified window. The prose still says all five printed values are too large. | valid (a correct published value declared wrong) | **ACCEPTED** |
| d02 | F12 "Correct": the faster-than-every-exponential class qualifier dropped, and the Scope line now says the caption is false in general | valid (algebraic-tail solutions exist; the record keeps the class as hypothesis 9) | **ACCEPTED** |
| d03 | F14: `fs_neg_wall_shear_two_decay` (two solutions with different wall shear) described as uniqueness | valid | **ACCEPTED** |
| d04 | the generated blocks of F13 and F14 swapped, so each finding shows the other branch's record | valid | **ACCEPTED** |
| d05 | F13: printed β changed −0.1988 → −0.1998 in the heading and Printed line (the record stays at −1988/10000) | valid (no attached solution exists at −0.1998: separation is near −0.19884) | **ACCEPTED** |
| d06 | F12: "more than one unit of the printed last digit" → "three units" (certified difference: 1.4 units) | valid | **ACCEPTED** |

**False acceptance on main: 6/6.** In plain words: every check on main stayed green while a verified finding
declared a correct published value wrong, put a finding's certificate under another finding, changed the row a
finding is about, and misdescribed a cited theorem.

## Repair (written after reading the report, not blind): `scripts/trust/check_findings.py`

The check is blocking in the trust step, and in the frozen step with `--base`, where the baseline may only shrink. It
has 12 controls in `--selftest`.

- FB1: a generated block may stand only in the section of its own finding (`F<k>_…` records in `### F<k>`).
- FB2: printed values are bound to Lean statements:
  - `d[src=H]`: d is a numeral of H's statement as CLAIMS.md prints it, including the bodies of PRINTED definitions.
  - `d[src>H]` / `d[src<H]`: H is universal, and d's whole rounding interval lies beyond a bound in H's conclusion. Hypotheses and existence statements never count.
- FB3: a bare `[src]` decimal on any line that states a finding (everything except the Referee and Fidelity-audit lines) is an error, unless it is listed in the shrink-only baseline.
- FB4: spelled-out sizes ("three units", "seven decimals") are baselined phrase by phrase, so a changed word fails.
- FB5: uniqueness words after a cited headline need H to state uniqueness. Generality words over an existential H must also say that something exists.
- FB6 (added after the full AFTER judge had started): a grow-only registry `scripts/trust/finding_class_phrases.txt` maps statement atoms to class phrases. Example: `M * (1 - p η) ≤ q η` ⇒ "faster-than-every-exponential". When a finding's record contains the atom, its Correct line must name the class. All four atoms match the F12–F14 records.

What the repair establishes on main:
- All five printed F13 values and the attached-flow value quoted in F14 now carry `[src>fs_neg_wall_shear_window]`. CI checks mechanically that each one's rounding interval lies above the certified window. Before, this rested on the prose sentence "the window also excludes the four other printed values".
- The F12–F14 β values and Fazio's reverse-flow value are bound to their records (`[src=…]`).

A side note from the red team was repaired in `check_numbers.py`. `role_of` labelled a relative difference
`(printed − q 0) / printed` as "printed"; it now labels it "difference(printed−free)", with a control. No existing
record changes.

## AFTER

- Full judge on a7b0125: the repaired tree, with the defects adapted to the bound tags. Results are in the "AFTER" lines below.
- Direct runs of the final `check_findings.py` on every variant:
  - d01 (value moved inside the window, tag kept) is rejected by FB2.
  - d01b (tag dropped to bare `[src]`) and d01c (judge's variant: the wrong value moved into the Correct line) are rejected by FB3.
  - d03 is rejected by FB5, d04 by FB1, d05 by FB2 and d05b (bare) by FB3, d06 by FB4.
  - d02 is rejected by FB6.
- After: 0/6 of the blind defects accepted, 0/9 counting the judge's variants. The AFTER figure is not blind: the repair was written after reading the defects.

AFTER (full judge, a7b0125: FB1–FB5, with FB3 then covering heading and Printed lines only. d01c and d02 against the final FB3/FB6 were judged directly, above):

- clean: ACCEPTED
- d01: CAUGHT — only by check_findings.py (FB rule as in the direct runs above)
- d01b: CAUGHT — only by check_findings.py (FB rule as in the direct runs above)
- d02: ACCEPTED
- d03: CAUGHT — only by check_findings.py (FB rule as in the direct runs above)
- d04: CAUGHT — only by check_findings.py (FB rule as in the direct runs above)
- d05: CAUGHT — only by check_findings.py (FB rule as in the direct runs above)
- d05b: CAUGHT — only by check_findings.py (FB rule as in the direct runs above)
- d06: CAUGHT — only by check_findings.py (FB rule as in the direct runs above)
- d02 was ACCEPTED here because FB6 did not exist yet; the final FB6 rejects it (direct run).

## Open

- FB6 reads only registered atoms and only the Correct line. Scope and Plain-words prose can still widen the class,
  as d02's second edit did. The structural fix is to generate a finding's Correct line from its record. A partial
  fix is a pinned `DecayClass p q` with a phrase.
- FB5 reads only parentheticals right after a cited headline. A misdescription in a separate sentence passes.
- 24 baselined bare printed values and spelled-out sizes in F1–F14 (`scripts/trust/findings_baseline.txt`).
