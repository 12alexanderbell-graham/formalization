# Red team against `scripts/external/replay.sh` (next-phase item 1, `EXTERNAL_CONCLUSIONS.md`)

Run 2026-11-26T1529Z, 2026-11-27 01:15–01:45Z, local (Lean 4.34.1, Mathlib d13f23b), on a copy of the
smallest outside closure (S1, OpenAI's Erdős 304: `OAI.NumberTheory.ShortEgyptian.Main` against
`ComparatorChallenges.ShortEgyptianFractions`). One defect planted per copy; each must FAIL at the step meant
to catch it. Generator, driver, planted files and raw results: `runs/2026-11-26T1529Z/redteam/`.

| # | planted defect | expected | result |
|---|---|---|---|
| P0 | none (control) | PASS | PASS (`COMPARE OK`, standard axioms) |
| P1 | weakened statement: solution's `main` gets an extra hypothesis `(2:ℕ) ≤ 1` (proof still compiles) | compare FAIL | FAIL: `TYPE differs: OAI.ShortEgyptian.main` |
| P2 | hidden `sorry`: proof of the dependency `main_upper_expansions` replaced by `sorry` | axioms FAIL | FAIL: axioms of `main` include `sorryAx` |
| P3 | extra axiom: `axiom cheat : False`, `main_upper_expansions := cheat.elim` | axioms FAIL; nanoda FAIL | FAIL: `OAI.ShortEgyptian.cheat` in the axioms; nanoda run separately on the export: `export file declares unpermitted axiom "OAI.ShortEgyptian.cheat"`, exit 1 |
| P4 | renamed definition: the challenge's `minLength` renamed `minLen` | compare FAIL | FAIL: `MISSING in solution: minLen`, `VALUE differs: maxMinLength` |
| P5 | `native_decide` inside a dependency's proof | axioms FAIL | FAIL: auxiliary axiom `…main_upper_expansions._native.native_decide.ax_1_1` (Lean 4.34 names the axiom per use, not `Lean.ofReduceBool`) |
| P7 | closure module whose `#print axioms` list wraps, non-standard axiom on line 1 | closure axioms FAIL | FAIL |
| P7b | same, non-standard axiom on line 2 of the wrapped list | closure axioms FAIL | FAIL (`check_axioms.py` joins the lines) |
| P8 | a closure using a reading theorem proved by `sorry` | closure axioms FAIL | FAIL: `sorryAx` |
| P8b | a sorry'd "closure" placed under a `Readings.*` module name (axiom check skipped for readings) | not a DONE | replay printed only `PASSED`; coverage reported the theorem UNCOVERED (0/1), so no false DONE, but the last line misled. **Fixed generally:** the replay's last line now states the coverage of the blind readings, `COMPLETE` / `INCOMPLETE` / `NONE`, "a DONE needs COMPLETE" (re-run: `INCOMPLETE`) |

Not planted: `implemented_by` (it changes compiled code only; the kernel never runs it, so it cannot make a
proof check; the advisory scan lists it). A kernel-invalid declaration cannot be planted from source (the
elaborator refuses it); leanchecker and nanoda replays of real closures stand for that check.

What this does and does not show: each planted defect was caught, at the intended step, by the same script
the verdicts used; it is one closure and one planter (this run), who knew the tool. Still open from the
conclusions: the coverage gate matches theorem names, not statements (item 4 of the plan); nanoda's
"Unable to print axioms" pretty-printer message is unexplained, but P3 shows nanoda's axiom whitelist is
enforced independently of it.
