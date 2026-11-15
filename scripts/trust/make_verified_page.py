#!/usr/bin/env python3
"""The page a reader of the verified findings reads is generated, with no author prose on it (rule FB26, part 3,
run 2026-11-15T1628Z). Blocking in CI (`--check`).

Why: FINDINGS.md mixes generated text (heading, Printed and Correct lines, certified blocks: FB10–FB13) with author
prose that no check reads, labelled as such (the **Unchecked notes** under each finding, FB10; the candidates
section under a fixed banner, FB25). Blind red-team rounds counted a false sentence under such a label as INVALID,
on the assumption that a reader who is told the notes are unchecked does not act on them. The reader-facing review of
run 2026-11-15T1628Z (`runs/2026-11-15T1628Z/t5/reader_brief.md`, `READERS.md`) measured that assumption with blind
readers who were asked which verified findings they could cite: one author line saying a verified finding was
WITHDRAWN made 3 of 3 readers drop it when the line stood in the labelled candidates section (two clean readers kept
it), and 3 of 3 again when it stood inside the finding's own labelled Unchecked notes. Every reader quoted the label
and the generated part correctly and still took the withdrawal: a label does not stop a reader from acting on a
claim that nothing generated contradicts. So the page a reader is pointed to holds no author prose at all.

What this script does: VERIFIED_FINDINGS.md = a fixed header (below) + for each verified finding of FINDINGS.md, in
order, exactly its generated part (the generated heading, the generated Printed and Correct lines, its certified
blocks: every line above its Unchecked-notes marker) + the generated section "## Certified numbers" of FINDINGS.md.
It fails closed: a finding whose part above the marker holds any line that is not a generated heading, a generated
Printed or Correct line, a blank line or a line of a certified block is an error (FB10 already forbids that in
FINDINGS.md; this script does not trust it). The notes and the candidates section never reach the page.

The Correct line on the page is RE-GENERATED, not copied (blind round AU, same run: all seven defects put author words
on the page through the one author-controlled input of the generators that reaches it, the class-phrase registry
`finding_class_phrases.txt`, by a forged brief -> reading -> copy route — "toy model illustration only with no bearing on
the published formula" as F2's class): on the page each class phrase is replaced by the fixed word `hypothesis` before
the Lean text it was registered for (`class: hypothesis `M * (1 - p η) ≤ q η`, …`). The registry decides only WHICH
Lean hypotheses are pointed at, never the words. FINDINGS.md keeps the phrases (FB6/FB9 there are unchanged).

  python3 scripts/trust/make_verified_page.py           # write VERIFIED_FINDINGS.md
  python3 scripts/trust/make_verified_page.py --check   # CI: the file equals what the script writes now
  python3 scripts/trust/make_verified_page.py --selftest

After `check_numbers.py --write` or `check_findings.py --write-layout`, run this script too (the author's
regeneration; the T5 judges run it with the others).
"""
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, "scripts", "trust"))
from check_findings import (NOTES_MARKER, PRINTED_GEN, CORRECT_GEN, NORECORD_CORRECT, generated_correct,  # noqa: E402
                            claims_blocks, load_phrases, sections_full, _span)

SRC = os.path.join(ROOT, "FINDINGS.md")
OUT = os.path.join(ROOT, "VERIFIED_FINDINGS.md")
VERIFIED_HEAD = "## Verified findings"
NUMBERS_HEAD = "## Certified numbers (generated from the Lean records; do not edit)"
GEN_HEADING = re.compile(r"^### F\d+ — generated heading \(do not edit\): \S")

HEADER = """# VERIFIED FINDINGS (generated; do not edit)

**What this page is (rule FB26, `scripts/trust/make_verified_page.py`; CI fails if the page differs from the script's output):** every line below is generated from Lean records of this repository — for each verified finding its generated heading (its Lean records and how each printed value is bound to a blind second reading), the generated *Printed* line (the printed values the records contain, the blind reading each agrees with, and the blind reader's own description of the source), the generated *Correct* line (what the records state: quantifier, the Lean hypotheses that restrict the class, direction) and the certified blocks (each number next to the Lean statement that certifies it, quoted from CLAIMS.md), then the certified-numbers table. **There is no author prose on this page.** Author notes (titles, scope, propagation, referee reports, status remarks) and candidates under verification are in `FINDINGS.md`; they are unchecked, and nothing written there changes what this page says. A finding is on this page exactly when it has Lean records in `Checked/Records/`; it leaves only when its records do.

A number is machine-checked only inside a block headed *Certified numbers (generated)*. Lean statements are checked by Lean (CI); what a Lean definition means is pinned and audited as described in `TRUST_MAP.md` and `CLAIMS.md`.
"""


class PageError(Exception):
    pass


NEUTRAL = "hypothesis"


def page_correct(sec, line, ctx):
    """The Correct line of `sec` as the page shows it: generated from the records with every class phrase replaced by
    the fixed word NEUTRAL before its Lean text. Fails closed unless FINDINGS.md's line is the generator's own output
    (so nothing but the phrases can differ)."""
    if line == NORECORD_CORRECT:
        return line
    cb, phrases, full = ctx
    body = full.get(sec)
    if body is None or generated_correct(sec, body, cb, phrases) != line:
        raise PageError(f"FB26: the Correct line of {sec} is not the generator's output (`check_findings.py "
                        f"--write-correct {sec}`)")
    tagged = [(a, "\x00" + str(i) + "\x00") for i, (a, _ph) in enumerate(phrases)]
    g = generated_correct(sec, body, cb, tagged)
    for i, (a, _ph) in enumerate(phrases):
        g = g.replace("\x00" + str(i) + "\x00 (Lean: " + _span(a) + ")", NEUTRAL + " " + _span(a))
    if "\x00" in g:
        raise PageError(f"FB26: a class phrase of {sec} could not be neutralised")
    return g


def context(text):
    claims = open(os.path.join(ROOT, "CLAIMS.md"), encoding="utf-8").read()
    return claims_blocks(claims), load_phrases(os.path.join(ROOT, "scripts", "trust", "finding_class_phrases.txt")), \
        sections_full(text)


def build(text, ctx=None, correct=None):
    correct = correct or page_correct
    if ctx is None and correct is page_correct:
        ctx = context(text)
    lines = text.split("\n")
    if VERIFIED_HEAD not in lines:
        raise PageError("FB26: FINDINGS.md has no line `## Verified findings`")
    i = lines.index(VERIFIED_HEAD)
    j = next((k for k in range(i + 1, len(lines)) if lines[k].startswith("## ")), len(lines))
    out = [HEADER.rstrip("\n"), "", VERIFIED_HEAD, ""]
    sec = None          # current finding id
    state = "out"       # out | gen | block | notes
    n_secs = 0
    for k in range(i + 1, j):
        l = lines[k]
        if l.startswith("### "):
            if sec is not None and state != "notes":
                raise PageError(f"FB26: section {sec} has no Unchecked-notes marker (line {k + 1})")
            if not GEN_HEADING.match(l):
                raise PageError(f"FB26: line {k + 1}: a level-3 heading in the verified section that is not a "
                                f"generated finding heading: {l[:80]!r}")
            sec = l.split()[1]
            state = "gen"
            n_secs += 1
            out += [l]
            continue
        if sec is None:
            if l.strip():
                raise PageError(f"FB26: line {k + 1}: text before the first finding of the verified section")
            continue
        if state == "notes":
            continue                       # author prose: never copied
        if state == "block":
            out.append(l)
            if l == "<!-- /certified -->":
                state = "gen"
            continue
        # state == "gen": the generated part of a finding
        if l == NOTES_MARKER:
            state = "notes"
            out.append("")
            continue
        if l == "" or PRINTED_GEN.match(l):
            out.append(l)
            continue
        if CORRECT_GEN.match(l):
            out.append(correct(sec, l, ctx))
            continue
        if re.fullmatch(r"<!-- certified: [A-Za-z0-9_ ]+? -->", l):
            out.append(l)
            state = "block"
            continue
        raise PageError(f"FB26: section {sec}, line {k + 1}: a line above the Unchecked-notes marker that is not "
                        f"generated (heading, Printed, Correct, certified block): {l[:80]!r}")
    if sec is not None and state != "notes":
        raise PageError(f"FB26: section {sec} has no Unchecked-notes marker")
    if n_secs == 0:
        raise PageError("FB26: no verified finding found")
    # collapse runs of blank lines
    page = re.sub(r"\n{3,}", "\n\n", "\n".join(out).rstrip("\n") + "\n")
    if NUMBERS_HEAD not in lines:
        raise PageError("FB26: FINDINGS.md has no generated certified-numbers section")
    m = lines.index(NUMBERS_HEAD)
    e = next((k for k in range(m + 1, len(lines)) if lines[k].startswith("## ")), len(lines))
    page += "\n" + "\n".join(lines[m:e]).rstrip("\n") + "\n"
    return page


def selftest():
    good = ("# FINDINGS\n\npre\n\n## Verified findings\n\n"
            "### F1 — generated heading (do not edit): records `F1_x`\n"
            "- **Printed (generated by x):** p\n- **Correct (generated from y):** c\n"
            "<!-- certified: F1_x -->\n- block line\n<!-- /certified -->\n" + NOTES_MARKER + "\n"
            "  - *(author)* **Title** (was C1): WITHDRAWN, do not cite\n\n"
            "## Candidates under verification (UNVERIFIED, not findings)\n\nC1 withdrawn\n\n"
            + NUMBERS_HEAD + "\n\n| t |\n")
    ident = lambda s, l, c: l  # noqa: E731  (synthetic sections: the Correct generator is tested on the real file below)
    p = build(good, correct=ident)
    ok = 0
    assert "WITHDRAWN" not in p and "C1 withdrawn" not in p and "block line" in p and "| t |" in p
    assert "- **Correct (generated from y):** c" in p
    ok += 1
    bad = [
        good.replace("- **Correct (generated from y):** c\n", "- **Correct:** c\n"),             # author line above marker
        good.replace(NOTES_MARKER + "\n", ""),                                                     # no marker
        good.replace("### F1 — generated heading (do not edit): records", "### F1 — the error"),  # author heading
        good.replace("## Verified findings\n\n", "## Verified findings\n\nintro prose\n\n"),      # prose before F1
        good.replace(NUMBERS_HEAD, "## Numbers"),                                                  # no numbers section
        good.replace("<!-- certified: F1_x -->\n", "<!-- certified: F1_x  -->x\n"),               # broken block opener
    ]
    for b in bad:
        try:
            build(b, correct=ident)
        except PageError:
            ok += 1
        else:
            raise AssertionError("selftest: control accepted:\n" + b)
    # real file: no registry phrase reaches the page, and a forged phrase (round AU d01) does not either
    real = open(SRC, encoding="utf-8").read()
    cb, phrases, full = context(real)
    page = build(real, (cb, phrases, full))
    for _a, ph in phrases:
        assert ph not in page, ph
    ok += 1
    forged = phrases + [("wₐ := -1 / 2", "toy model illustration only with no bearing on the published formula")]
    import check_findings as _cf
    secs = [k for k in full if "wₐ := -1 / 2" in "".join(cb.get(r, "") for r in re.findall(r"`(F\d+_\w+)`", full[k]))]
    real2 = _cf.write_correct(real, secs, cb, forged) if secs else real
    if secs:
        page2 = build(real2, (cb, forged, sections_full(real2)))
        assert "toy model" in real2 and "toy model" not in page2
        assert page2 == page or "hypothesis `wₐ := -1 / 2`" in page2
        ok += 1
    # a hand-edited Correct line fails closed
    bad_c = real.replace("lies above the", "lies below the", 1)
    try:
        build(bad_c, (cb, phrases, sections_full(bad_c)))
    except PageError:
        ok += 1
    else:
        raise AssertionError("selftest: hand-edited Correct line accepted")
    print(f"make_verified_page selftest: {ok} controls passed")


def main():
    if "--selftest" in sys.argv:
        selftest()
        return 0
    try:
        page = build(open(SRC, encoding="utf-8").read())
    except PageError as e:
        print(e)
        return 1
    if "--check" in sys.argv:
        cur = open(OUT, encoding="utf-8").read() if os.path.exists(OUT) else None
        if cur != page:
            print("FB26: VERIFIED_FINDINGS.md differs from `python3 scripts/trust/make_verified_page.py` "
                  "(the reader page is generated; run the script and commit the result)")
            return 1
        print("make_verified_page: VERIFIED_FINDINGS.md is current")
        return 0
    with open(OUT, "w", encoding="utf-8") as f:
        f.write(page)
    print(f"make_verified_page: wrote VERIFIED_FINDINGS.md ({page.count(chr(10))} lines)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
