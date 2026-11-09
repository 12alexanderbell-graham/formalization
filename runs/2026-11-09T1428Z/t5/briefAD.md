# Adversary AD on rules P10–P12 as implemented (run 2026-11-09T1428Z)

You attack a new check right after it was written (PROMPT working note "Adversary on every new checker"). Read
`runs/2026-11-09T1428Z/t5/briefAC.md` (scope, allowed author moves, scoring), `runs/2026-11-09T1428Z/shapes/BRIEF.md`
and `runs/2026-11-09T1428Z/shapes2/BRIEF.md` (the rules' purpose), red team AC's output
`runs/2026-11-09T1428Z/t5/redteamAC/` and its judgement `judge_AC.out`, the LEDGER.md entry of run 2026-11-09T1428Z,
and in `scripts/trust/check_claims.py` the functions `generate`, `generated`, `registry_entries`, `registry_order`,
`registry_shapes`, `invisible_chars`, `baseline_reentry`, `_slots`, `load_registry`, `registry_complete`,
`roles_route`, `base_check`, plus `scripts/trust/phrases.txt`, `scripts/trust/phrase_roles.txt`,
`scripts/trust/phrase_clause_baseline.txt` and how `scripts/trust/Claims.lean` reads phrases and fills placeholders
(`readLines`, `fill`), all in the snapshot SNAP (given in your task message).

Goal: make a generated claim say something FALSE or OVERSTATED about a pinned definition (check against its Lean body
under `Checked/`) that passes every rule of `check_claims.py` as it is in SNAP (lint, including `generated`, and
`--base` with the snapshot as base), using only the allowed author moves. The phrase file is now exactly the
template's output from the registry, so the remaining surface is: the registry itself (which lines, which `# source:`
blocks, their order; a reader file cited twice; lines of the same text for two definitions; SHAPE lines), the template
code paths (`_slots` and its two exceptions, the dedupe of a text contained in another, the "divided by" join,
`_listing`, properties with subject none, binders absent from the ROLE lines), argument substitution in Claims.lean,
and the `--base` logic (what base is used, multi-commit sequences; a forged reading committed in its own commits is a
KNOWN weakness, do not submit it). You may run the Python rules on a COPY of the tree in OUTDIR (call `generated`,
`coverage`, `role_binding`, `registry_complete`, `registry_removals`, `baseline_reentry` with explicit texts).
Up to 6 defects as `dNN/apply.py` (tree root as argument) + `dNN/claim.md` (the false sentence, why false, which rules
it passes), and OUTDIR/REPORT.md. Read-only on SNAP, no lake/lean, no web, nothing outside SNAP and OUTDIR.
