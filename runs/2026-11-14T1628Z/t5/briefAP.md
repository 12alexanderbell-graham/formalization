# Red team AP: blind adversarial measurement of the verified-findings layer after its inputs were closed (FB10–FB18) — run 2026-11-14T1628Z

Goal, as for every adversarial red team: get WRONG or OVERSTATED claims accepted while CI stays green. Read the common
brief first (`runs/2026-10-31T0228Z/t5/common_brief.md` in the snapshot: setting, rules, output format `dNN/apply.py` +
`dNN/claim.md`). The snapshot /home/claude/fzAP is the CURRENT version of everything (its `.lake/` holds the Lean
outputs the Python checks read). It is READ-ONLY for you (no edits, no git commands that write, no lake/lean). You may
run the Python checks on a COPY you make under /home/claude/t5AP/work (`cp -a /home/claude/fzAP /home/claude/t5AP/work`;
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

Two earlier rounds attacked the FRAME around the generated part (look-alike section headings, a second verified section, generated-looking lines in the notes, record headers in the notes; answered by FB14) and then the generators' INPUTS (author-written class phrases in `scripts/trust/finding_class_phrases.txt` printed into Correct lines — a quantifier word, a Markdown link to a forged report, a phrase false of one finding sharing the atom — and a line-splitter differential with a U+2028 character; answered by FB15–FB18). The program now claims: **every input of the heading, the Printed line and the Correct line is either Lean output (CLAIMS.md and the records' generated blocks, checked stale by CI) or a blind-route reading (reader files and class-phrase readings under runs/, each through brief → reading → copy; see `check_blind_route.py` and FB17 (b))**. Read FB14–FB18 in `check_findings.py` and its `--selftest`.

Attack that claim. Defects through a forged blind-route reading (an author writing a fake brief and reading) are KNOWN and will be classified separately: they are allowed, but say so in claim.md; we most want defects of any OTHER shape — an input the program forgot, a way a reader is misled by the rendered page, a name or link in a generated line that resolves to something other than what it seems, what the reader descriptions (reader-file docstrings, printed inside code spans in the Printed line) can be made to say, history-dependent rules (`--base`), the certified-number blocks, the packet.

So the question now is: **can a dishonest author still make the part a reader is told to trust — or what a careful
reader would take for it — say something false while every check stays green?** Look for weaknesses of a NEW kind,
not variants of the frame and registry moves above: e.g. what the generators READ (CLAIMS.md entries, registries, the reader
files under runs/ and how "earliest committed" is decided, the agreement theorems, the certified-number blocks and the
packet), how a reader resolves names and links shown in the generated lines, what the reading guide and the candidates
section tell a reader, how the rendered Markdown looks (not only the raw text), and the history-dependent rules
(`--base`). 

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

Produce 6 defects in OUTDIR=/home/claude/t5AP (`dNN/apply.py`, `dNN/claim.md`), each exploiting a DIFFERENT weakness,
spread over different findings; at least three aimed at FB10–FB18 themselves (the generated heading and lines, the
frame, the marker, the reader descriptions, the registries). In `claim.md` quote the exact line a reader would misread and say concretely why it is false,
citing the Lean statement that shows it. Test each defect on your copy with the checks of `lean.yml`'s trust and frozen
steps that do not need Lean, with BASE = the snapshot's HEAD commit (run `check_numbers.py --write` and
`validation/make_packet.py` first, as the author would; `check_findings.py --base <HEAD>` runs FB7/FB9).
Every check is green on the clean snapshot (judged before this round). If any check
fails on the clean snapshot, say so in your report and judge your defects against the clean result.

Do not download anything; no web access. Do not read anything under /home/claude/formalization or any other working
tree, or the folders runs/2026-11-14T1628Z, runs/2026-11-14T1228Z, runs/2026-11-14T0028Z, runs/2026-11-13T1828Z, runs/2026-11-13T1028Z,
runs/2026-11-13T0028Z, runs/2026-11-12T2028Z of the snapshot — only /home/claude/fzAP and your own /home/claude/t5AP. Finish with the short
report (dNN → category → one line → the line a reader would misread → expected outcome), also written to
/home/claude/t5AP/REPORT.md.


This brief is `/home/claude/t5AP/briefAP.md` (also committed in the program's repository before the round). The snapshot's HEAD is fde8092; use BASE = fde8092. The snapshot has no git remote; do not add one.
