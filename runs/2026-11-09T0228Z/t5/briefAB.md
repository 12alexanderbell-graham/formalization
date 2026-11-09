# Adversary AB on rules P7/P8 as implemented (run 2026-11-09T0228Z)

You attack a new check right after it was written (PROMPT working note "Adversary on every new checker"). Read
`runs/2026-11-09T0228Z/t5/briefAA.md` (scope, allowed author moves, scoring), `runs/2026-11-09T0228Z/clauses/BRIEF.md`
(the rule's purpose), the LEDGER.md entry of run 2026-11-09T0228Z, `scripts/trust/check_claims.py` (functions
`p7_tokens`, `coverage`, `_verb_ok`, `registry_complete`, `registry_removals`, `load_registry`, `role_binding`),
`scripts/trust/phrases.txt` and `scripts/trust/phrase_roles.txt` in the snapshot SNAP (given in your task message).

Goal: make a phrase say something FALSE about its definition (check against the Lean body printed in CLAIMS.md / the
definition under `Checked/`) that passes every rule of `check_claims.py` as it is in SNAP (lint and `--base`), using
only the allowed author moves. Typical routes to try: composing blind texts of the same definition into a false
sentence with the allowed connectives or the template verb; filling a binder slot of a CLAUSE with a different
argument; tokenizer edge cases (NFKC, apostrophes, hyphens, digits glued to letters, placeholders inside words);
the registry (adding lines, comments, a new `# source:` block — the route brief → reading → copy is enforced by
`--base`; a forged reading committed in its own commit is a KNOWN weakness, do not submit it); omission that makes the
remaining text false. You may run the Python rules on a COPY of the tree in OUTDIR (`.lake/phrases.jsonl` is absent:
call `coverage`, `role_binding`, `registry_complete`, `formula_in_phrase`, `duplicate_phrases` directly on your
modified phrases and registry text). Up to 6 defects as `dNN/apply.py` (tree root as argument) + `dNN/claim.md` (the
false sentence, why false, which rules it passes), and OUTDIR/REPORT.md. Read-only on SNAP, no lake/lean, no web,
nothing outside SNAP and OUTDIR.
