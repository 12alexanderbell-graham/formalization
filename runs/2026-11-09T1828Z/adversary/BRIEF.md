# Adversary AE brief (run 2026-11-09T1828Z): attack rule P13, certified phrase lines

You are an adversary for a trust system that turns Lean 4 theorems into plain-words claims (`CLAIMS.md`) that scientists
are told to rely on. The plain words of a pinned definition ("phrase") are lines written by blind readers
(`scripts/trust/phrase_roles.txt`, SIGN and CLAUSE lines), assembled mechanically (`scripts/trust/check_claims.py`,
rules P1–P12). The new rule P13 (snapshot commit 86c07c9) adds: every SIGN/CLAUSE line must be proved about the
definition by a Checked theorem named in `scripts/trust/phrase_certs.txt` (Lean file `Checked/Trust/PhraseCerts.lean`),
or be listed in the shrink-only `scripts/trust/phrase_cert_baseline.txt`. `scripts/trust/Claims.lean` resolves each
certificate theorem, requires its statement to use the definition, prints its hypotheses after the phrase in CLAIMS.md
and writes the full generated statement to PHRASE_LINES.md. `check_claims.py --base B` forbids baseline growth and
CERT removal since commit B.

Read: `scripts/trust/check_claims.py` (functions `certified_lines`, `certs_base`, `_controls_p13`, `base_check`, `lint`,
`registry_complete`, `baseline_reentry`), `scripts/trust/Claims.lean` (the P13 parts: `certs`, `certNote`,
PHRASE_LINES.md), `scripts/trust/phrase_certs.txt`, `scripts/trust/phrase_cert_baseline.txt`,
`Checked/Trust/PhraseCerts.lean`, the registry `scripts/trust/phrase_roles.txt` and its header. The snapshot is a plain
directory (no git history); assume the base commit B is the snapshot itself.

Task: find up to 6 concrete defects: sequences of edits an author could commit after B such that every P1–P13 check
(as implemented) passes, yet CLAIMS.md shows a reader line that is false of the Lean definition, or overstates what is
certified, or hides a condition under which a certified line fails. Also report any certified line in
`phrase_certs.txt` whose theorem does not in fact prove what the line says (a mismatch), and any line in the baseline's
group B ("no property of the value") that does state a property. For each: the exact edits (file, old → new), which
check you expect to pass and why, and what false meaning reaches a reader. Rank by severity. Do not modify any file
outside your output; write your report as plain text in your final message. Be concrete; no general advice.
