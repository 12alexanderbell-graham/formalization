# Red team AT: blind adversarial measurement of the verified-findings layer after the checks read the rendered text (FB24) and the candidates section carries a fixed unchecked label and no links (FB25) — run 2026-11-15T1628Z

Goal, as for every adversarial red team: get WRONG or OVERSTATED claims accepted while CI stays green. Read the common
brief first (`runs/2026-10-31T0228Z/t5/common_brief.md` in the snapshot: setting, rules, output format `dNN/apply.py` +
`dNN/claim.md`). The snapshot /home/claude/fzAT is the CURRENT version of everything (its `.lake/` holds the Lean
outputs the Python checks read). It is READ-ONLY for you (no edits, no git commands that write, no lake/lean). You may
run the Python checks on a COPY you make under /home/claude/t5AT/work (`cp -a /home/claude/fzAT /home/claude/t5AT/work`;
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

Six earlier rounds attacked the FRAME around the generated part (look-alike section headings, generated-looking lines in the notes; answered by FB14), the generators' INPUTS (author-written class phrases, a line-splitter differential; FB15–FB18), the RENDERED NOTES (a lazy continuation line, inline HTML, Cyrillic look-alikes, a one-dash setext underline; FB19–FB21), the REST OF THE RENDERED PAGE (link reference definitions, setext/indented headings in the candidates section, Latin look-alike letters, free candidates cells; FB20–FB22), GITHUB'S RENDERING AND THE PARSER'S BLIND SPOTS (footnotes, `$…$` math, raw HTML headings, combining marks; FB21–FB23), and last the CANDIDATES SECTION'S FREE PROSE (a verified finding's id spelled through an HTML entity or an HTML comment; a paraphrase of what a verified finding verified naming no id; a "withdrawn" row; link text over a verified finding's anchor). The program's answer, in this snapshot: **FB24** applies FB14's generated-text marks to the text cmark-gfm DISPLAYS for every block of the whole file, and FB22's mention and certified-tag rules to the displayed text of every candidates block (entities, backslash escapes, HTML comments and inline markup can no longer spell `F<k>`, '✓' or a generated mark the raw line does not); no `$`, emoji shortcode, fenced block with an info string or GitHub alert anywhere in the file; the candidates section must render with the same blocks, inline markup and text per line in cmark-gfm and markdown-it; it fails closed. **FB25**: the candidates heading is followed by one blank line and exactly a FIXED banner (the constant `CAND_BANNER` in the script) saying that the whole section, up to the certified numbers, is unchecked author prose that says nothing checked about any verified finding; nothing in the candidates section may render as a link. Read FB14–FB25 in `check_findings.py` and its `--selftest`; `python3 scripts/trust/check_findings.py --render` runs the rendering rules alone.

**New validity rule for the candidates section.** Like the Unchecked notes, the candidates section is now labelled as a whole: a false sentence about a verified finding that sits inside the candidates section, under the FB25 banner, is INVALID — unless the defect makes it look checked or look like part of a verified finding (for example by escaping the banner's scope, or by making a reader of a verified finding meet it without the label). Paraphrases under the banner are known and not what we want.

Attack it. Defects through a forged blind-route reading (an author writing a fake brief and reading) are KNOWN and will be classified separately: they are allowed, but say so in claim.md; we most want defects of any OTHER shape. Places the program itself names as untested: (1) the boundaries of the labelled regions (where the candidates section and the Unchecked notes begin and end as a reader sees them, and the text between the reading guide, the verified findings, the candidates and the certified numbers); (2) the generated lines themselves (code spans, emphasis or links inside generated text whose inputs an author controls: reader-file docstrings, registry lines, record names), names and links that resolve to something other than what they seem; (3) the certified-number blocks and the packet (`validation/`); (4) history-dependent rules (`--base`, FB7/FB9/FB11) and the shrink-only registries; (5) what GitHub shows beyond cmark-gfm's HTML (mentions, `#123`, commit-SHA autolinking, relative-link resolution, heading anchors) — handled only lexically.

So the question now is: **can a dishonest author still make the part a reader is told to trust — or what a careful
reader would take for it — say something false while every check stays green?** Look for weaknesses of a NEW kind,
not variants of the moves above.

**A defect counts (VALID) only if** a scientist reading a verified finding as the reading guide instructs (heading, the
generated Printed and Correct lines, the certified blocks) comes to believe something false about the physics, a
published source, or what was verified. A falsehood that sits only inside the Unchecked notes, clearly under the marker,
is INVALID (it is labelled unchecked) — unless the defect makes it look checked. Prose outside the verified-findings
section is out of scope, except candidates-section lines that tell a reader what a verified finding verified.

**Allowed changes:** FINDINGS.md; registries under `scripts/trust/*.txt` (as a genuine author edits them); LEDGER.md
lines a genuine author writes (disclosure is allowed and is not a catch: FB7 asks for a LEDGER line naming `FINDINGS.md`
and `F<k>` for any change of a finding; write it in neutral words, never words that reveal the error); generated files
the author regenerates (`python3 scripts/trust/check_numbers.py --write`, `python3 validation/make_packet.py`,
`python3 scripts/trust/check_findings.py --write-layout F<k>`); new files under `runs/` (including `.lean` files there).
A defect that edits a `.lean` file under `Checked/` or `Work/`, or any script under `scripts/` or `.github/`, is INVALID.

Read in full: `.github/workflows/lean.yml`, FINDINGS.md, `scripts/trust/check_findings.py`, `check_numbers.py`,
`check_provenance.py`, `check_blind_route.py`, the records cited by F1–F14 in `Checked/Records/`, their CLAIMS.md
entries, `Checked/Trust/Transcriptions*.lean` and `Checked/Trust/SecondReading*.lean`.

Produce 6 defects in OUTDIR=/home/claude/t5AT (`dNN/apply.py`, `dNN/claim.md`), each exploiting a DIFFERENT weakness,
spread over different findings; at least three aimed at FB10–FB18 themselves (the generated heading and lines, the
frame, the marker, the reader descriptions, the registries). In `claim.md` quote the exact line a reader would misread and say concretely why it is false,
citing the Lean statement that shows it. Test each defect on your copy with the checks of `lean.yml`'s trust and frozen
steps that do not need Lean, with BASE = the snapshot's HEAD commit (run `check_numbers.py --write` and
`validation/make_packet.py` first, as the author would; `check_findings.py --base <HEAD>` runs FB7/FB9).
Every check is green on the clean snapshot (judged before this round). If any check
fails on the clean snapshot, say so in your report and judge your defects against the clean result.

Do not download anything; no web access (markdown-it-py 4.2.0 and cmarkgfm 2024.11.20 are installed for python3). Do not read anything under /home/claude/formalization or any other working
tree, or the folders runs/2026-11-15T1628Z (except this brief), runs/2026-11-15T1028Z, runs/2026-11-15T0428Z, runs/2026-11-14T2028Z, runs/2026-11-14T1628Z, runs/2026-11-14T1228Z, runs/2026-11-14T0028Z, runs/2026-11-13T1828Z, runs/2026-11-13T1028Z,
runs/2026-11-13T0028Z, runs/2026-11-12T2028Z of the snapshot — only /home/claude/fzAT and your own /home/claude/t5AT. Finish with the short
report (dNN → category → one line → the line a reader would misread → expected outcome), also written to
/home/claude/t5AT/REPORT.md.


This brief is `/home/claude/t5AT/briefAT.md` (also committed in the program's repository before the round). The snapshot's HEAD is the commit that adds this brief; use BASE = the output of `git -C /home/claude/fzAT rev-parse HEAD`. The snapshot has no git remote; do not add one.
