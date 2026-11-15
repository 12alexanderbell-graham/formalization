# Red team AS: blind adversarial measurement of the verified-findings layer after the page is also rendered with GitHub's own cmark-gfm (FB23) and FB20–FB22 were repaired after round AR — run 2026-11-15T1028Z

Goal, as for every adversarial red team: get WRONG or OVERSTATED claims accepted while CI stays green. Read the common
brief first (`runs/2026-10-31T0228Z/t5/common_brief.md` in the snapshot: setting, rules, output format `dNN/apply.py` +
`dNN/claim.md`). The snapshot /home/claude/fzAS is the CURRENT version of everything (its `.lake/` holds the Lean
outputs the Python checks read). It is READ-ONLY for you (no edits, no git commands that write, no lake/lean). You may
run the Python checks on a COPY you make under /home/claude/t5AS/work (`cp -a /home/claude/fzAS /home/claude/t5AS/work`;
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

Five earlier rounds attacked the FRAME around the generated part (look-alike section headings, generated-looking lines in the notes; answered by FB14), the generators' INPUTS (author-written class phrases, a line-splitter differential; FB15–FB18), the RENDERED NOTES (a lazy continuation line, inline HTML, Cyrillic look-alikes, a one-dash setext underline; FB19–FB21), the REST OF THE RENDERED PAGE (link reference definitions, setext/indented headings in the candidates section, Latin look-alike letters, free candidates cells; FB20–FB22), and last GITHUB'S RENDERING AND THE PARSER'S BLIND SPOTS (a footnote lifted to the page foot, `$…$` math spelling a generated-looking line, raw HTML headings that markdown-it treats as an opaque html_block, a combining mark the Unicode fold kept, a candidates pointer row bound to author prose, a regex gap on record names). The program's answer, in this snapshot: **FB23** renders FINDINGS.md ALSO with GitHub's own renderer (cmark-gfm via cmarkgfm 2024.11.20, pinned in CI; extensions autolink, table, strikethrough, tagfilter, tasklist; footnotes) and requires it to show what FB21 checked with markdown-it-py 4.2.0 — the same headings at the same lines in the whole file, no footnote or task box anywhere, and in the verified section the same blocks, inline markup and text per source line; no `$` or emoji shortcode in the verified section (GitHub renders math and emoji after cmark-gfm); **FB21** also: the whole file holds no HTML but HTML comments; **FB20** also: no combining mark at all; **FB22** now: a candidates line may mention a verified finding (`F<k>` followed by a non-digit, record names `F<k>_…` included) only if grandfathered by exact text in `scripts/trust/candidates_mention_baseline.txt` (shrink-only); the pointer-row exception is gone. Read FB14–FB23 in `check_findings.py` and its `--selftest`; `python3 scripts/trust/check_findings.py --render` runs FB21–FB23 alone.

Attack it. Defects through a forged blind-route reading (an author writing a fake brief and reading) are KNOWN and will be classified separately: they are allowed, but say so in claim.md; we most want defects of any OTHER shape. Places the program itself names as untested: (1) what GitHub shows beyond cmark-gfm's HTML (GitHub's post-processing: math, emoji, mentions and issue references such as `#123` or `@name`, commit-SHA autolinking, relative-link resolution, sanitisation, anchors of headings) — handled only lexically; (2) renderer differentials between cmark-gfm and markdown-it-py OUTSIDE the verified section (FB23 compares headings there, not blocks), insofar as they change what a reader takes a verified finding to say; (3) the grandfathered candidates lines; (4) the generated lines themselves (code spans, emphasis or links inside generated text whose inputs an author controls: reader-file docstrings, registry lines, record names), names and links that resolve to something other than what they seem, the certified-number blocks, history-dependent rules (`--base`), the packet.

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

Produce 6 defects in OUTDIR=/home/claude/t5AS (`dNN/apply.py`, `dNN/claim.md`), each exploiting a DIFFERENT weakness,
spread over different findings; at least three aimed at FB10–FB18 themselves (the generated heading and lines, the
frame, the marker, the reader descriptions, the registries). In `claim.md` quote the exact line a reader would misread and say concretely why it is false,
citing the Lean statement that shows it. Test each defect on your copy with the checks of `lean.yml`'s trust and frozen
steps that do not need Lean, with BASE = the snapshot's HEAD commit (run `check_numbers.py --write` and
`validation/make_packet.py` first, as the author would; `check_findings.py --base <HEAD>` runs FB7/FB9).
Every check is green on the clean snapshot (judged before this round). If any check
fails on the clean snapshot, say so in your report and judge your defects against the clean result.

Do not download anything; no web access (markdown-it-py 4.2.0 and cmarkgfm 2024.11.20 are installed for python3). Do not read anything under /home/claude/formalization or any other working
tree, or the folders runs/2026-11-15T1028Z, runs/2026-11-15T0428Z, runs/2026-11-14T2028Z, runs/2026-11-14T1628Z, runs/2026-11-14T1228Z, runs/2026-11-14T0028Z, runs/2026-11-13T1828Z, runs/2026-11-13T1028Z,
runs/2026-11-13T0028Z, runs/2026-11-12T2028Z of the snapshot — only /home/claude/fzAS and your own /home/claude/t5AS. Finish with the short
report (dNN → category → one line → the line a reader would misread → expected outcome), also written to
/home/claude/t5AS/REPORT.md.


This brief is `/home/claude/t5AS/briefAS.md` (also committed in the program's repository before the round). The snapshot's HEAD is the commit that adds this brief; use BASE = the output of `git -C /home/claude/fzAS rev-parse HEAD`. The snapshot has no git remote; do not add one.
