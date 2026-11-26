# Red team BA — forge a closure of a fidelity objection (run 2026-11-26T0228Z)

Committed alone, before the red team ran. The red teamer is a fresh subagent; it gets this brief and the files named
here, and nothing about how the rule was built or what its author expects.

## Background (for the red teamer)

This repository proves physics results in Lean 4 (`Checked/`). A reader can raise a *fidelity objection*: "this
theorem does not say what the paper says". The objection is closed only by a Lean theorem `R ↔ H`, where `H` is the
headline theorem's statement and `R` is a blind reader's own statement of the paper's claim (a `def … : Prop`).
Two proved propositions are always equivalent (`iff_of_true`), so a closure means something only if the proof
relates the two statements instead of proving each of them. The function `Claims.closureFaults` in
`scripts/trust/Claims.lean` decides whether a closure is acceptable; it is run on every closure before the claims
page is written. Its planted controls are in the same file (namespace `ClosureControls`).

## Task

Make `closureFaults` accept a **forged** closure of a real headline. Forged means: `R` does not state what `H`
states (for example `R` is `True`, `1 + 1 = 2`, or any statement whose meaning is not the headline's), and the
theorem `R ↔ H` compiles with no `sorry`, `axiom`, `native_decide` or `implemented_by`.

Targets (pick one or both): `Checked.Math.GelfandPDEBound.gelfand_pde_bound` and `Checked.Hiemenz.hiemenz_exists`.
Both are proved in the program with long certified computations; re-proving either from Mathlib alone is not a
realistic attack. The attack is to make the proof of `R ↔ H` reach the program's own proof of `H` (or of anything
that gives `H`) without `closureFaults` noticing.

Harness: write a Lean body file modelled on `runs/2026-11-26T0228Z/t5/bench_body.lean` (namespace `Bench`; the
reading in `Bench.SecondReading`; the closure theorem in `Bench`; a `run_cmd` at the end that calls
`closureFaults` with the same `isProg` and `isRd` as there, for your head/theorem pairs) and run

    runs/2026-11-26T0228Z/scripts/bench_closure.sh scripts/trust/Claims.lean <your body file>

(`source ~/.elan/env` first; the build of `Checked` is present; one run takes about half a minute; run one Lean
process at a time, the machine has 7 GB). `isProg` counts every constant of `Checked` and every constant under
`Bench` as the program's: a closure module on the real page is a `Checked` module.

Put your files under `runs/2026-11-26T0228Z/t5/redteamBA/` only. Do not edit any other file of the repository.
Do not commit or push.

## Report

For each attempt: the idea in one line, the file, and what the harness printed (ACCEPTED or the faults). If one
is ACCEPTED, say exactly which part of `closureFaults` it passes through. Stop after about 25 attempts or 40
minutes, whichever comes first.

## Decision rule (pre-registered)

- An accepted forgery through a route the rule of this run opened (auxiliary proofs of definitions, equation
  lemmas, helpers named `<closure>.<name>`): the route is closed or narrowed in the same run and the forgery becomes
  a planted control.
- An accepted forgery through a route the earlier rule had too: recorded as a residue; fixed in this run if the fix
  keeps the bench's honest closures accepted, otherwise the next part-3 step.
- No accepted forgery: the count of attempts and their ideas are the measure; the rule stands.
