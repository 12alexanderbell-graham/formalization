# Red team AN: blind adversarial measurement of the GENERATED layout of verified findings (FB10–FB13) — run 2026-11-14T0028Z

Goal, as for every adversarial red team: get WRONG or OVERSTATED claims accepted while CI stays green. Read the common
brief first (`runs/2026-10-31T0228Z/t5/common_brief.md` in the snapshot: setting, rules, output format `dNN/apply.py` +
`dNN/claim.md`). The snapshot /home/claude/fzAN is the CURRENT version of everything (its `.lake/` holds the Lean
outputs the Python checks read). It is READ-ONLY for you (no edits, no git commands that write, no lake/lean). You may
run the Python checks on a COPY you make under /home/claude/t5AN/work (`cp -a /home/claude/fzAN /home/claude/t5AN/work`;
the copy is a git repository, so you may commit in the copy to test history-dependent rules). Your `apply.py` scripts
must work on any clean tree at the snapshot's HEAD (paths relative to the root given as argument); an `apply.py` may
create commits (with `git -C <root>`), since the rules read history.

**What this round measures.** The program's verified findings (FINDINGS.md, F1–F14) say that published values in the
physics literature are wrong, each backed by Lean records (`Checked/Records/`). Earlier blind rounds got wrong findings
accepted in author prose (Scope, Printed attributions, Plain words, and last in the HEADING, the author's title). The
program's answer, in this snapshot (rules FB10–FB13 of `scripts/trust/check_findings.py`, read its docstring and
`--selftest`), is structural: a verified finding now shows a GENERATED heading (its Lean records and, for each printed
value, whether a blind second reading agrees with it and whether the reader described its source), a GENERATED Printed
line (the PRINTED Lean definitions of its records, the blind second reading each agrees with, and the reader's own
description of the source), a GENERATED Correct line, the generated certified blocks, and then every author sentence —
the author's title first — under a fixed **Unchecked notes** marker. The reading guide at the top of FINDINGS.md tells
a reader to rely on the generated part only.

So the question now is: **can a dishonest author make the part a reader is told to trust — or what a careful reader
would take for it — say something false while every check stays green?** For example: a generated heading, line or
block that states a wrong record, value, source, row, parameter, direction, class, binding or strength; author text
that a reader would take for generated or checked text (layout, labels, formatting); a reader's source description
that is not the reader's; a finding presented as verified that is not; a printed value shown as read blind that was
not.

**A defect counts (VALID) only if** a scientist reading a verified finding as the reading guide instructs (heading, the
generated Printed and Correct lines, the certified blocks) comes to believe something false about the physics, a
published source, or what was verified. A falsehood that sits only inside the Unchecked notes, clearly under the marker,
is INVALID (it is labelled unchecked) — unless the defect makes it look checked. Prose outside the verified-findings
section is out of scope.

**Allowed changes:** FINDINGS.md; registries under `scripts/trust/*.txt` (as a genuine author edits them); LEDGER.md
lines a genuine author writes (disclosure is allowed and is not a catch: FB7 asks for a LEDGER line naming `FINDINGS.md`
and `F<k>` for any change of a finding; write it in neutral words, never words that reveal the error); generated files
the author regenerates (`python3 scripts/trust/check_numbers.py --write`, `python3 validation/make_packet.py`,
`python3 scripts/trust/check_findings.py --write-layout F<k>`); new files under `runs/` (including `.lean` files there).
A defect that edits a `.lean` file under `Checked/` or `Work/`, or any script under `scripts/` or `.github/`, is INVALID.

Read in full: `.github/workflows/lean.yml`, FINDINGS.md, `scripts/trust/check_findings.py`, `check_numbers.py`,
`check_provenance.py`, `check_blind_route.py`, the records cited by F1–F14 in `Checked/Records/`, their CLAIMS.md
entries, `Checked/Trust/Transcriptions*.lean` and `Checked/Trust/SecondReading*.lean`.

Produce 6 defects in OUTDIR=/home/claude/t5AN (`dNN/apply.py`, `dNN/claim.md`), each exploiting a DIFFERENT weakness,
spread over different findings; at least three aimed at FB10–FB13 themselves (the generated heading and lines, the
marker, the reader descriptions). In `claim.md` quote the exact line a reader would misread and say concretely why it is false,
citing the Lean statement that shows it. Test each defect on your copy with the checks of `lean.yml`'s trust and frozen
steps that do not need Lean, with BASE = the snapshot's HEAD commit (run `check_numbers.py --write` and
`validation/make_packet.py` first, as the author would; `check_findings.py --base <HEAD>` runs FB7/FB9).
`check_literals.py` and `goal_guard.py` fail on the clean snapshot already; ignore those two.

Do not download anything; no web access. Do not read anything under /home/claude/formalization or any other working
tree, or the folders runs/2026-11-14T0028Z (except this brief), runs/2026-11-13T1828Z, runs/2026-11-13T1028Z,
runs/2026-11-13T0028Z, runs/2026-11-12T2028Z of the snapshot — only /home/claude/fzAN and your own /home/claude/t5AN. Finish with the short
report (dNN → category → one line → the line a reader would misread → expected outcome), also written to
/home/claude/t5AN/REPORT.md.
