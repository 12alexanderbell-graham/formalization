# Adversary AD report (rules P10-P12 as implemented, snapshot 9189018)

Method: read the brief, AC's report and judge output, the LEDGER entry, `check_claims.py` (all functions named), the
phrase/registry files, `Claims.lean` (`readLines`, `fill`, `atom`), `check_reader_frozen.py` and the workflow lines that
call `check_claims.py`. Each defect: `dNN/apply.py <root>` run on a fresh copy of SNAP's `scripts/`, `runs/`, `LEDGER.md`
(no git: SNAP is read-only), then `check_claims._controls()`, `duplicate_phrases`, `formula_in_phrase`, `load_registry`,
`role_binding`, `coverage`, `registry_complete`, `generated()`, `head_noun` (U2, glossary), and the `--base` functions with
the snapshot's files as base (`baseline_reentry`, `registry_removals`, baseline growth, changed-phrase vs LEDGER). Result for
all four: 0 problems; the phrase file is the output of `--generate` (so P11 is satisfied by construction). Not run: Lean,
`.lake/phrases.jsonl` (P2 `spec_vocabulary`, the `rests_on` half of the glossary lint), `roles_route` (needs git; it only
looks at ADDED registry lines: d01 adds none, d02 3, d03 1, d04 4, each to be carried by brief -> reading -> copy commits).
Controls: `_controls()` passes on every modified tree (they read the real CLAUSES.txt, which no defect modifies).

| dNN | weakness | one line | generated text | under the snapshot rules | P10/P11 as implemented |
|---|---|---|---|---|---|
| d01 | registry block order (reader file cited twice) + dedupe + glue | CLAUSES.txt cited, SYMBOLS order-2 line, CLAUSES cited again from the same line: the repeated line is dropped and "divided by the n-th power of the Hubble rate" is glued to the order-2 symbol clause. Only existing readings, no line added or removed | cosmoCoeff: "... (n-th time derivative of the scale factor over the scale factor; The order 2 coefficient is minus the deceleration parameter usually written q divided by the n-th power of the Hubble rate; ...)" | passes everything; no route needed | survives |
| d02 | exclusion baseline keyed by exact text | second differently worded reading of IsCriticalIsotherm, IsMaxwellCoexistence, omega0 restates three excluded overclaims ("an inflection point of the isotherm with horizontal tangent", "the same as the two phases having equal chemical potential", "above one exactly when the curvature constant is positive"); P9 forces the file in, the baseline cannot grow | the three phrases end with these clauses | passes; route (brief, reading, copy) to be followed | survives |
| d03 | template: dedupe of line 1 + glue of line 2 on an honest reading | narrow formula reader for cosmoCoeff (two true lines) appended after SYMBOLS | "... The order 5 coefficient is the lerk parameter usually written l divided by the Hubble rate to the power n" | passes; one added registry line (route) | survives (the template makes the sentence) |
| d04 | exclusion keyed by (definition, text) | reader of the siblings lumDistFlat and comoving writes the hypothesis lines excluded for lumDist/angDist | "...; emission time is not later than observation time; requires a positive continuous scale factor between emission and observation" on both | passes; route | survives; severity low-medium (hypotheses shown as properties) |

Ranking by value under P10/P11: d01 (no new reading at all) > d03 (true inputs, false output) > d02 > d04.

## Observed, not submitted
- Old reader `.txt` files are not frozen: `check_reader_frozen` F2 covers `.lean` files only, and `roles_route` skips a
  source that was not ADDED since base (`rc is None: continue`). An in-place edit that keeps the SET of lines (reordering
  lines of CLAUSES.txt/ROLES.txt) changes the order P11b treats as the reader's, with no route check. It is limited because
  `_controls_p10_p12` uses the real CLAUSES.txt (cosmoCoeff lines must stay adjacent and in order); I found no reorder
  that yields a clearly false sentence, so no defect. Content edits are caught by `registry_removals`.
- `registry_entries` indexes lines with `split("\n")`, `load_registry` and `registry_complete` with `splitlines()`: a
  reader line containing U+2028 etc. gives pieces with idx = -1, exempt from P11b and from the glue test (needs a forged
  reader file, so not submitted); `registry_complete` ignores reader lines with 5 or 7+ parts.
- When several readers give a ROLE for the same binder, `load_registry` keeps the last in registry order and shows only it;
  no disagreement check (needs a wrong reading, so the known class).
- `fill` in Claims.lean substitutes placeholders one after another: a printed argument containing `{t}` (e.g. a singleton
  set literal) would be re-substituted. No current headline does; not tested (no Lean).
- `base_check` falls back to HEAD~1 for a zero/unknown base (a push of several commits to a new branch is judged
  against the last commit only).
- Pre-existing (snapshot): the glued/ordered clause lists read "positive curvature constant gives above one" (false at
  hubble = 0) and the ambiguous-parse clauses are kept out only by exact-line exclusion (the cause of d02/d04).
New facts for memory: none (memory not read).
