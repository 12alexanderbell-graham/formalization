# Run 2026-11-27T1028Z

**THE RESULT:** part 3 (what a reader may rely on without trusting the authors): the last three pinned definitions with no blind specification reading (the F(R) expansion-rate equation, the F(R) master equation and the dust density of Bamba et al. 2012 §XI) read by three sourced blind readers (Sonnet, Opus, Haiku), each reading closed in Lean against the program's definition. (Stub; filled as the run goes.)

**What can a scientist now trust without checking it themselves, that they could not before?** (filled at the end)

**Weakest unchecked step:** (filled at the end)

## Start
- 10:27Z. Session clone detached; `git checkout -B main origin/main` (9f275ee); `scripts/start_run.sh` (elan 4.35.0, Mathlib cache, commit-msg hook).
- **`LOCK` held by run 2026-11-27T0828Z** (started 08:28Z, heartbeat 10:01Z, 26 min old; task: H₂⁺ angular certificate, then records): alive, so this run takes the auditor role (48.4): writes only in `runs/2026-11-27T1028Z/` and appends to `CHANGELOG.md`; no `STATE.md`, `Checked/`, `scripts/` until the LOCK is free.
- **`EXTERNAL_LOCK` held by run 2026-11-27T0628Z** (heartbeat 10:22Z, 5 min old; targets R and O): the external targets stay with it (PROMPT 11).
- Env: repo ok (`add_repo` not exposed in this session; the clone was present, push works). Local Lean 4.35.0 with the Mathlib cache; `lake build Checked.Cosmography.FRCosmo` started for the closures.

## Bottleneck
Section Next (b) of `runs/2026-11-27T0228Z/README.md` (part 3): 71 of the 494 pinned definition uses on the claims page rest on a specification only the program wrote: `FRCosmo.FriedmannEq`, `FRCosmo.MasterEq`, `FRCosmo.rhoM`. They are disjoint from both live runs' tasks. Yes (sourced readers' specifications are met by and determine the definitions) → those uses gain a blind reading; no → the definition differs from an independent reading of its own source, proved, and the page must show it.

## What we did
- Sources (`sources/`, outside the readers' folders, B5): `bamba2012_1205.3421v3.md`, a byte-identical copy of run 0428Z's verbatim LaTeX excerpt of arXiv 1205.3421v3 (§II metric, §VIII.C, §X, §XI through (11.6); e-print sha256 in its header).
- Briefs `specI/briefI.md` (Sonnet), `specJ/briefJ.md` (Opus), `specK/briefK.md` (Haiku): three items each, quantity + source + Lean type, never the formula; committed before the readers run.
