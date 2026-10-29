# STATE

Last updated: 2026-10-30, setup (chat session, not a scheduled run).

## Phase
S1 DONE (judge proven, see LEDGER). Next: S2, pick target 1 (at most 2 runs, annex 53.1).

## Target
None yet.

## What exists
- Governance: verbatim original constitution (SHA-256 matches Alexander's recorded hash), Formalization Edition annex v3.1, operative core, all joined in `CONSTITUTION_COMPLETE.md`; checksums in `governance/SHA256SUMS`.
- Lean project: toolchain `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0` (manifest pinned), libraries `Checked` (namespace `Checked`) and `Work` (namespace `Work`), one placeholder theorem each.
- CI judge, proven on positive controls: blocking checks are build, leanchecker, axiom-audit (allowlist propext, Classical.choice, Quot.sound), forbidden-token grep. axiom-audit only audits declarations in namespace `Checked`, so everything promoted must live there.
- Known gap: nanoda (independent type checker) is report-only because of an export-format mismatch with Lean v4.35.0. Repair when there is spare capacity, and before any finding is reported.
- Physlib is not yet a dependency. When added, pin a commit; at setup Physlib master was `2725b6f621901d4cd330869e9b77105045c1582e` (2026-10-29), same toolchain and Mathlib v4.35.0. Adding it means updating `lake-manifest.json` by hand if local Lean is unavailable (copy Physlib's own manifest entries and add a `physlib` git entry at the pinned rev).
- Typical CI time with cache: about 3 minutes.

## Known environment facts
- In the setup chat session, installing Lean locally via the elan installer was refused by the environment's safety check (twice). Scheduled runs may hit the same refusal; CI on branches is the fallback (annex XLIX).

## Open questions for Alexander
None.

## Exact next step
S2: build TARGETS.md, pick target 1, freeze its first milestone (small enough for the full pipeline within 3 runs, annex 53.2), message Alexander with the pick.
