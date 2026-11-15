# Red team AR: blind adversarial measurement of the verified-findings layer after the WHOLE page is rendered and whitelisted in CI (FB19–FB22 as repaired after round AQ) — run 2026-11-15T0428Z

Goal, as for every adversarial red team: get WRONG or OVERSTATED claims accepted while CI stays green. Read the common
brief first (`runs/2026-10-31T0228Z/t5/common_brief.md` in the snapshot: setting, rules, output format `dNN/apply.py` +
`dNN/claim.md`). The snapshot /home/claude/fzAR is the CURRENT version of everything (its `.lake/` holds the Lean
outputs the Python checks read). It is READ-ONLY for you (no edits, no git commands that write, no lake/lean). You may
run the Python checks on a COPY you make under /home/claude/t5AR/work (`cp -a /home/claude/fzAR /home/claude/t5AR/work`;
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

Four earlier rounds attacked the FRAME around the generated part (look-alike section headings, generated-looking lines in the notes; answered by FB14), the generators' INPUTS (author-written class phrases, a line-splitter differential; FB15–FB18), the RENDERED NOTES (a lazy continuation line, inline HTML, Cyrillic look-alikes, a one-dash setext underline; FB19–FB21), and last the REST OF THE RENDERED PAGE (link reference definitions elsewhere in the file turning certified tags into links with false hover titles, a setext/indented heading in the candidates section rendering a second verified section, Latin look-alike letters, free cells and other arrows in the candidates section). The program's answer, in this snapshot: **FB21** renders the WHOLE of FINDINGS.md with a pinned CommonMark renderer (markdown-it-py 4.2.0; plain CommonMark and CommonMark with GFM tables/strikethrough) and whitelists it — no link reference definition anywhere, every rendered heading is a frame heading, a finding heading or a candidate heading at its own line, no link, image or inline HTML in the generated part, the verified section's block structure exactly the one the line model assumes; **FB20** (non-ASCII Latin letters only as ASCII letters with marks; marks matched after NFKD with combining marks dropped; no letters outside Latin/Greek/mathematical alphabets, no invisible format characters); **FB22** (no certified tag `[✓…]` in the candidates section; a candidates line that mentions a verified finding `F<k>` is either grandfathered by exact text in `scripts/trust/candidates_mention_baseline.txt`, shrink-only, or a bare pointer row `| C<n> | — | — | → **F<k>** |` bound to that finding's title note "(was …)"). The candidates section is IN SCOPE this round as far as it tells a reader what a verified finding verified. Read FB14–FB22 in `check_findings.py` and its `--selftest`; `python3 scripts/trust/check_findings.py --render` runs FB21/FB22 alone.

Attack it. Defects through a forged blind-route reading (an author writing a fake brief and reading) are KNOWN and will be classified separately: they are allowed, but say so in claim.md; we most want defects of any OTHER shape. Two places the program itself names as untested: (1) what GitHub's own renderer (cmark-gfm: extended autolinks of bare URLs and www., footnotes `[^x]`, task lists, alerts such as `> [!NOTE]`, emoji shortcodes, math `$…$` and ```` ```math ````, sanitised HTML, relative-link resolution in the repository) shows differently from markdown-it-py's CommonMark — a reader opens FINDINGS.md on GitHub; (2) the grandfathered candidates lines (free text kept by exact match) and whatever else of the candidates section a reader may take as telling what a verified finding verified. Also: what a reader sees in the rendered generated lines themselves (code spans, links, emphasis inside generated text whose inputs an author controls), the reader descriptions printed in the Printed line, names and links that resolve to something other than what they seem, the certified-number blocks, history-dependent rules (`--base`), the candidates section's other lines, the packet.

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

Produce 6 defects in OUTDIR=/home/claude/t5AR (`dNN/apply.py`, `dNN/claim.md`), each exploiting a DIFFERENT weakness,
spread over different findings; at least three aimed at FB10–FB18 themselves (the generated heading and lines, the
frame, the marker, the reader descriptions, the registries). In `claim.md` quote the exact line a reader would misread and say concretely why it is false,
citing the Lean statement that shows it. Test each defect on your copy with the checks of `lean.yml`'s trust and frozen
steps that do not need Lean, with BASE = the snapshot's HEAD commit (run `check_numbers.py --write` and
`validation/make_packet.py` first, as the author would; `check_findings.py --base <HEAD>` runs FB7/FB9).
Every check is green on the clean snapshot (judged before this round). If any check
fails on the clean snapshot, say so in your report and judge your defects against the clean result.

Do not download anything; no web access (markdown-it-py 4.2.0 is installed for python3). Do not read anything under /home/claude/formalization or any other working
tree, or the folders runs/2026-11-15T0428Z, runs/2026-11-14T2028Z, runs/2026-11-14T1628Z, runs/2026-11-14T1228Z, runs/2026-11-14T0028Z, runs/2026-11-13T1828Z, runs/2026-11-13T1028Z,
runs/2026-11-13T0028Z, runs/2026-11-12T2028Z of the snapshot — only /home/claude/fzAR and your own /home/claude/t5AR. Finish with the short
report (dNN → category → one line → the line a reader would misread → expected outcome), also written to
/home/claude/t5AR/REPORT.md.


This brief is `/home/claude/t5AR/briefAR.md` (also committed in the program's repository before the round). The snapshot's HEAD is the commit that adds this brief; use BASE = the output of `git -C /home/claude/fzAR rev-parse HEAD`. The snapshot has no git remote; do not add one.
