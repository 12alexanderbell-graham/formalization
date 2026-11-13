# Blind red team AJ — the verified-findings layer after FB1–FB6 (run 2026-11-13T0028Z): results

Red team: Sonnet, blind, brief `briefAJ.md` (committed first, 3f66ca9), read-only snapshot 3f66ca9 with the Lean
outputs (`.lake/*.jsonl`, `*.tsv`) of CI's `author-files` artifact of 43311405425 (50d4d16; no headline changed
between 50d4d16 and the snapshot). Lean-free round: defects may change FINDINGS.md, registries and LEDGER only. The
red team took 5 min; its output is committed verbatim in `redteamAJ/` (9b62f2d) before judging.

Judge: `judge_aj.sh` (copy of run 2028Z's `judge_ai.sh`): after the author regenerates the certified blocks and the
packet, it runs `goal_guard.py`, `make_packet.py --check` and every `python3` command of CI's trust step and frozen
step (read from `lean.yml`, BASE = 3f66ca9) on a worktree at the snapshot. Raw output: `before_judge.txt`,
`after_judge.txt`.

| d | defect | valid? | BEFORE | AFTER |
|---|---|---|---|---|
| d01 | F12 Scope: the printed separation value said to be wrong "for every zero-wall-shear solution, whatever its approach (exponential or algebraic)"; the record keeps the faster-than-every-exponential class as a hypothesis and the finding itself says algebraic-tail solutions exist there | valid | **ACCEPTED** | CAUGHT (FB7) |
| d02 | F13 Printed: 0.005226 and 0.005225 swapped between Asaithambi 2005 and Salama 2004 (both stay above the window, so FB2 holds) | valid (wrong source attribution) | **ACCEPTED** | CAUGHT (FB7) |
| d03 | F1 Correct: cubic coefficient of m₀ changed 81/4 → 81/2 (contradicts the finding's own −455/4 at Ω = 1) | valid | **ACCEPTED** | CAUGHT (FB7) |
| d04 | F4 Scope: "Lean covers every curvature"; the Lean evidence is flat FLRW only | valid | **ACCEPTED** | CAUGHT (FB7) |
| d05 | F14 Scope: "the reverse-flow branch is unique (proved)"; the record is existence only, and the section cites a two-solution theorem | valid | **ACCEPTED** | CAUGHT (FB7) |
| d06 | F10 Printed: the two printed η₂₀ values swapped between Ω = 0.041 and 0.25 (both baselined values) | valid | **ACCEPTED** | CAUGHT (FB7) |

**False acceptance on main (blind): 6/6.** In plain words: a day after the findings layer got its own check, every
check on main still stayed green while a verified finding widened its class, misattributed printed values between
sources and parameters, changed a coefficient of the correct formula, and claimed Lean coverage and uniqueness the
Lean does not give. Each defect sat in a part of a finding that no rule reads (FB6 reads only the Correct line, FB5
only parentheticals, FB2/FB3 bind a value but not its source or row).

## Repair (after reading the report, so AFTER is not blind): FB7 in `scripts/trust/check_findings.py`

Rules over free prose have now lost two blind rounds on this layer (AI, AJ: 12/12) and, before that, rounds F–V on
docstrings; each rule closed the last round's shapes only. FB7 does not read the words: with `--base` (CI's frozen
step) a verified finding whose prose (generated blocks excluded) differs from BASE — changed, new or removed — needs a
LEDGER line added since BASE naming `FINDINGS.md` and the finding. Silent rewording is impossible; a disclosed one is
on the record for a reader and a later audit. Controls: three rejected cases and three clean twins (`--selftest`, 18
controls).

AFTER (full judge with the new script copied into the judge tree): clean ACCEPTED, d01–d06 CAUGHT, each only by
`check_findings.py --base` (FB7). **0/6, not blind.**

## Open
- The words of a NEW finding, or of a disclosed rewording, are still the author's. The structural repair remains to
  generate the Correct and Scope lines from the record (class from the hypotheses, existence vs universal from the
  quantifier) and to bind a printed value to its source and row (a registry `value → source, row` read blind).
