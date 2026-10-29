# STATE

Last updated: 2026-10-30, setup (chat session, not a scheduled run).

## Phase
Setup. S1 (prove the judge works) and S2 (pick target 1) from `PROMPT.md` are not done.

## Target
None yet.

## What exists
- Governance: verbatim original constitution (SHA-256 matches Alexander's recorded hash), Formalization Edition annex v3.0, operative core.
- Lean project: toolchain `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`, libraries `Checked` and `Work`, one placeholder theorem each.
- CI workflow `.github/workflows/lean.yml` written but **never run**. Unknown whether every lean-action check (axiom-audit, leanchecker, nanoda) works on this project as configured.
- Physlib is not yet a dependency. When added, pin to a commit; at setup time Physlib `master` was `2725b6f621901d4cd330869e9b77105045c1582e` (2026-10-29), which uses the same toolchain and Mathlib `v4.35.0`.

## Known environment facts
- In the setup chat session, installing Lean locally via the elan installer was refused by the environment's safety check (twice). Scheduled runs may hit the same refusal; CI is the fallback (annex XLIX).

## Open questions for Alexander
None.

## Exact next step
S1: push, confirm green CI on both jobs, then run the two positive controls.
