# Formalization program: run instructions

Read fresh every run. Alexander may edit this file at any time; the latest version wins.

## Standing instructions

1. Follow `governance/02_OPERATIVE_CORE.md` every run. On the first run, after lost context, or after the governance files change, read `governance/01_CONSTITUTION_FORMALIZATION.md` and `governance/00_ORIGINAL_CONSTITUTION.md` in full.
2. Domain: physics. Use Physlib (github.com/leanprover-community/physlib) and Mathlib as the base libraries.
3. Work the whole run on the single most consequential step. No one-minute runs, no restarting from scratch, no going in circles.
4. Local Lean: try installing it with the official `elan` installer from github.com/leanprover/elan (Alexander has authorized this). If the environment refuses, do not try to get around the refusal: use the CI judge on GitHub instead, and note it in the run record.
5. If the repository can't be reached, still run: do what is possible and put the results in your final message, marked NOT SAVED.
6. Message Alexander only under annex L.2. Result first, bullets, any question in bold.

## Current phase: setup, then target selection

`STATE.md` says what is done. Until these are done, they come first:

**S1. Prove the judge works.**
- Push a commit and confirm both CI jobs (`work`, `checked`) go green on the trivial placeholder theorem.
- Positive controls on a throwaway branch: a `sorry` in `Checked` must make CI fail; a custom `axiom` used in `Checked` must make CI fail. Record the run IDs. Delete nothing; leave the branches.
- If any check in the workflow doesn't work as intended, fix the workflow and log it in `LEDGER.md` as an integrity event (annex 39.5).

**S2. Pick target 1** (annex XLII).
- Build `TARGETS.md`: ranked candidates, each with importance, checkability (what Mathlib/Physlib already have), error potential, prior-art check, first milestone, and who it helps.
- Mine Physlib's `TODO` and `informal_lemma` items as one source, but not the only one.
- Pick target 1, write the case and the eight items of annex 36.5 in `STATE.md`, add Physlib as a dependency if the target needs it (pin the commit), freeze the first milestone's statement.
- Message Alexander with the pick (it is a target change under L.2).

After S1 and S2, the phase is: work the target.
