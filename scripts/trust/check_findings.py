#!/usr/bin/env python3
"""Verified findings are bound to Lean, not only their certified numbers (part 3, run 2026-11-12T2028Z). Blocking in CI.

Why: blind red team AI (Sonnet, snapshot 7ad53ed; `runs/2026-11-12T2028Z/t5/`) attacked the verified-findings
section of FINDINGS.md, the layer that says "this published value is wrong". check_numbers.py certifies the
numbers inside the generated blocks; the words and the printed values around them were free. The red team moved
a refuted printed value onto the correct side of the certified window (d01), swapped the generated blocks of two
findings (d04), changed the printed β of a row (d05), changed a spelled-out count of units (d06) and described a
non-uniqueness theorem as uniqueness (d03). Rules (scope: "## Verified findings" up to the next "## " heading,
generated blocks excluded; a section is `### F<k> …` up to the next `### `):

  FB1  a generated block `<!-- certified: R … -->` in section F<k> names only records `F<k>_…` (a record certifies
       the finding whose section shows it, d04); every record name starts with `F<n>_`.
  FB2  printed values may be bound to a Lean statement (H: a headline's short name, as CLAIMS.md heads it, cited in
       the same section in backticks, or a record of the section):
         `d[src=H]`  the value of d is a numeral of H's statement as CLAIMS.md prints it (the statement and the
                     bodies of the definitions it lists, e.g. a PRINTED value or the β of the equation);
         `d[src>H]`  H is a universal statement ("**For every**") whose conclusion bounds some quantity X above by
                     U (`X < U` or `X ≤ U`) and the whole rounding interval of d (d ± ½·10⁻ᵏ, k printed decimals)
                     lies at or above U: the printed value is too large for every solution H speaks of;
         `d[src<H]`  likewise below a lower bound L of the conclusion.
       A hypothesis never counts as a bound (only the "**then**" part), and an existential statement never refutes.
  FB3  in a section with a generated block, a bare `[src]` decimal outside the Referee and Fidelity-audit lines
       (heading, Printed, Correct, Lean evidence, Classification, Plain words) is an error unless listed in the shrink-only
       baseline `scripts/trust/findings_baseline.txt` (`src <section> <value>`): a printed value the finding relies on
       is bound by FB2 or visibly unbound (d01, d05).
  FB4  a spelled-out count next to a unit of size ("three units", "seven decimals", "fourth significant digit") is
       an error unless baselined (`words <section> <phrase>`): sizes are certified numbers in generated blocks (d06).
  FB5  a parenthetical right after a cited headline, `` `H` (…) ``, that calls something unique (unique…, "the only",
       "exactly one", "at most one"; not "non-unique…" or "not unique") needs H to state uniqueness (`∃!`, or a
       universal statement with an equation and no `≠` in its conclusion); one that generalises (every, any, all,
       each, whatever) over an existential H must also say that something exists (d03; the shape rule of
       check_prose.py applied to the words that describe a cited theorem in a finding).

  FB6  for each line `<atom> => <phrase>` of the grow-only registry `scripts/trust/finding_class_phrases.txt`: when a
       record of a finding's section contains the atom anywhere in its statement (CLAIMS.md), the finding's
       "Correct" line contains the phrase (d02: a class qualifier dropped from the prose that states the finding).
       Known limit: only registered atoms are read, and only the Correct line (Scope prose is free).

  FB7  (run 2026-11-13T0028Z, after blind round AJ: 6/6 accepted against FB1–FB6, every defect in prose no rule read
       — a class widened in Scope, two printed values swapped between their sources or between their parameters, a
       fraction of a correct formula changed, Lean coverage and uniqueness claimed in Scope) the prose of a verified
       finding is frozen: with --base SHA, every section F<k> whose prose (generated blocks excluded, trailing
       blanks ignored) differs from its text at SHA — changed, new or removed — needs a line added to LEDGER.md since
       SHA that names `FINDINGS.md` and the finding in backticks (`F<k>`): a reworded finding is disclosed, never
       silent. Known limit: the words of a new or disclosed finding are still the author's (the disclosure is what
       is checked, not the content).

  FB8  (run 2026-11-13T1028Z, after blind round AK: 6/6 accepted with disclosure — a new finding F15 with no record
       and a "Checked, CI green" evidence line, a coefficient of a correct formula changed, a correct value moved, the
       direction of a certified difference flipped, a correct published table declared wrong, a scope consequence
       added; all disclosed by neutral LEDGER lines, as FB7 allows) every verified finding shows a generated block
       of at least one record of its own (`F<k>_…`), unless baselined (`norecord F<k>`, shrink-only): a finding is
       verified by a Lean record, never by prose that cites other theorems (AK d01).
  FB9  with --base: a verified finding whose Correct line is new or differs from BASE has as its Correct line exactly
       the line GENERATED from its records (`--write-correct F<k>` writes it): for each record, its quantifier, the
       class phrases of FB6 the statement carries, and for every certified difference whose rounding interval
       excludes 0 the direction (which side lies above), the size left to the certified block (AK d02–d05). The
       author's words on that line can no longer change; unchanged legacy Correct lines stay frozen by FB7. Known
       limit: Scope, Classification, Plain-words, Printed and Lean-evidence lines of a disclosed change are still
       the author's (AK d06).

  python3 scripts/trust/check_findings.py              rules FB1–FB6, FB8 on FINDINGS.md (reads CLAIMS.md)
  python3 scripts/trust/check_findings.py --base SHA   also: the baseline gained no line since SHA; FB7, FB9
  python3 scripts/trust/check_findings.py --write-correct F<k> [F<j> …]   replace those findings' Correct lines by
                                                       the generated ones (an author edit: FB7 still wants a LEDGER line)
  python3 scripts/trust/check_findings.py --selftest   controls only
"""
import re
import subprocess
import sys
from fractions import Fraction

FINDINGS = "FINDINGS.md"
CLAIMS = "CLAIMS.md"
BASELINE = "scripts/trust/findings_baseline.txt"
PHRASES = "scripts/trust/finding_class_phrases.txt"
NORECORD = "scripts/trust/findings_norecord_baseline.txt"  # FB8, shrink-only
DASHES = "−–—‐‑‒-"
SUP = "⁰¹²³⁴⁵⁶⁷⁸⁹"
NUM = r"[" + DASHES + r"]?\d+(?:\.\d+)?(?:×10[⁻⁺]?[" + SUP + r"]+)?"
SRC = re.compile(r"(?<![\w.])(" + NUM + r")\[src(?:([=<>])([A-Za-z0-9_]+))?\]")

CARD = ("zero one two three four five six seven eight nine ten eleven twelve thirteen fourteen fifteen sixteen "
        "seventeen eighteen nineteen twenty thirty forty fifty sixty seventy eighty ninety hundred thousand million "
        "dozen several few").split()
ORD = ("first second third fourth fifth sixth seventh eighth ninth tenth eleventh twelfth thirteenth fourteenth "
       "fifteenth sixteenth seventeenth eighteenth nineteenth twentieth").split()
UNITW = r"(units?|digits?|decimals?|places?|orders?\s+of\s+magnitude|percent|per\s+cent|times|sigma|σ|figures?)"
WORDS = re.compile(r"(?i)\b(" + "|".join(CARD + ORD) + r")\b((?:[\s-]+[\w']+){0,2}?)[\s-]+" + UNITW + r"\b")
UNIQ = re.compile(r"(?i)(?<![-\w])(?<!non-)(unique\w*|the only|exactly one|at most one)\b")
UNIV = re.compile(r"(?i)\b(every|any|all|each|whatever)\b")
EXIST = re.compile(r"(?i)\b(exist\w*|there (is|are)|some|an? (example|solution|instance)|two|witness\w*)\b")


def norm(tok):
    for c in DASHES:
        tok = tok.replace(c, "-")
    return tok


def prose_value(tok):
    """(exact value, decimals k) of a prose number such as −0.1988 or 6.61×10⁻⁶."""
    tok = norm(tok)
    exp = 0
    if "×10" in tok:
        tok, e = tok.split("×10")
        e = e.replace("⁻", "-").replace("⁺", "")
        exp = int("".join(str(SUP.index(c)) if c in SUP else c for c in e))
    dec = len(tok.split(".")[1]) if "." in tok else 0
    return Fraction(tok) * Fraction(10) ** exp, dec - exp


LEAN_NUM = re.compile(r"(-\s*\(\s*|-)?(\d+(?:\.\d+)?(?:e-?\d+)?)(?:\s*/\s*(\d+(?:\.\d+)?(?:e-?\d+)?))?")


def lean_values(text):
    out = set()
    for m in LEAN_NUM.finditer(text):
        v = Fraction(m.group(2)) / (Fraction(m.group(3)) if m.group(3) else 1)
        out.add(-v if m.group(1) else v)
        out.add(v)  # the unsigned literal as well (a sign may sit in the operator before it)
    return out


def lean_value(s):
    s = s.strip()
    m = LEAN_NUM.fullmatch(s.replace("(", "").replace(")", "") if s.startswith("-(") else s)
    if not m:
        return None
    v = Fraction(m.group(2)) / (Fraction(m.group(3)) if m.group(3) else 1)
    return -v if m.group(1) else v


def claims_blocks(text):
    """short name -> CLAIMS.md block text (statement part, before the author's paraphrase)."""
    out = {}
    for m in re.finditer(r"^## `([^`]+)`\n(.*?)(?=^## `|\Z)", text, re.S | re.M):
        body = m.group(2).split("Author's paraphrase")[0]
        out.setdefault(m.group(1), body)
    return out


def bounds(block):
    """(universal?, unique?, then-text, {quantity: (lower, upper)}) of a CLAIMS block."""
    universal = "**For every**" in block.split("**then**")[0] and "**It holds that**" not in block
    then = block.split("**then**", 1)[1] if "**then**" in block else block.split("**It holds that**", 1)[-1]
    then = then.split("\nwhere\n")[0]
    lo, hi = {}, {}
    for span in re.findall(r"`([^`]+)`", then):
        for a, op, b in [re.fullmatch(r"(.+?) (<|≤) (.+)", span).groups()] if re.fullmatch(r"(.+?) (<|≤) (.+)", span) else []:
            va, vb = lean_value(a), lean_value(b)
            if va is not None and vb is None:
                lo[b.strip()] = max(lo.get(b.strip(), va), va)
            elif vb is not None and va is None:
                hi[a.strip()] = min(hi.get(a.strip(), vb), vb)
    q = {x: (lo.get(x), hi.get(x)) for x in set(lo) | set(hi)}
    unique = "∃!" in block or (universal and " = " in then and "≠" not in then)
    return universal, unique, then, q


def verified_sections(text):
    i = text.find("\n## Verified findings")
    if i < 0:
        return []
    j = text.find("\n## ", i + 1)
    scope = text[i:j if j >= 0 else len(text)]
    secs = []
    for m in re.finditer(r"^### (F\d+)\b(.*?)(?=^### |\Z)", scope, re.S | re.M):
        body = m.group(0)
        blocks = re.findall(r"^<!-- certified: ([A-Za-z0-9_ ]+?) -->$", body, re.M)
        prose = re.sub(r"^<!-- certified:.*?^<!-- /certified -->$", "", body, flags=re.S | re.M)
        secs.append((m.group(1), prose, [r for b in blocks for r in b.split()]))
    return secs


def load_baseline(path=BASELINE, text=None):
    if text is None:
        try:
            text = open(path, encoding="utf-8").read()
        except FileNotFoundError:
            text = ""
    return {l.strip() for l in text.splitlines() if l.strip() and not l.startswith("#")}


def load_phrases(path=PHRASES, text=None):
    if text is None:
        try:
            text = open(path, encoding="utf-8").read()
        except FileNotFoundError:
            text = ""
    out = []
    for l in text.splitlines():
        if l.strip() and not l.startswith("#") and " => " in l:
            a, b = l.rsplit(" => ", 1)
            out.append((a.strip(), b.strip()))
    return out


def check(findings, claims, baseline, phrases=()):
    errs = []
    cb = claims_blocks(claims)
    for sec, prose, records in verified_sections(findings):
        # FB1
        for r in records:
            m = re.match(r"F(\d+)_", r)
            if not m:
                errs.append(f"FB1 {sec}: record {r} is not named F<n>_…: name a finding's record after its finding")
            elif f"F{m.group(1)}" != sec:
                errs.append(f"FB1 {sec}: the generated block of record {r} stands in section {sec}; it certifies "
                            f"finding F{m.group(1)} (move the `<!-- certified -->` marker to its own section)")
        # FB6
        correct = " ".join(l for l in prose.split("\n") if l.startswith("- **Correct"))
        for r in records:
            for atom, phrase in phrases:
                if r in cb and atom in cb[r] and phrase not in correct:
                    errs.append(f"FB6 {sec}: record {r} states `{atom}` but the Correct line does not name its class "
                                f"('{phrase}', scripts/trust/finding_class_phrases.txt)")
        cited = set(re.findall(r"`(?:[A-Za-z0-9_.]*\.)?([A-Za-z0-9_]+)`", prose)) | set(records)
        for line in prose.split("\n"):
            # every line that states the finding; the referee and audit lines report how it was checked
            claimline = not (line.startswith("- **Referee") or line.startswith("- **Fidelity"))
            # code spans are not prose numbers
            s = re.sub(r"`[^`]*`", lambda mm: " " * len(mm.group()), line)
            for t in SRC.finditer(s):
                num, op, h = t.group(1), t.group(2), t.group(3)
                v, k = prose_value(num)
                if op is None:
                    if records and claimline and f"src {sec} {norm(num)}" not in baseline:
                        errs.append(f"FB3 {sec}: {num}[src] is a printed value the finding relies on but bound to no "
                                    f"Lean statement: write {num}[src=H], [src>H] or [src<H] (FB2) with H a headline "
                                    f"cited in this section")
                    continue
                if h not in cited:
                    errs.append(f"FB2 {sec}: {num}[src{op}{h}]: {h} is not cited in this section (cite it in backticks)")
                    continue
                if h not in cb:
                    errs.append(f"FB2 {sec}: {num}[src{op}{h}]: no CLAIMS.md entry `{h}`")
                    continue
                universal, unique, then, q = bounds(cb[h])
                if op == "=":
                    if v not in lean_values(cb[h]):
                        errs.append(f"FB2 {sec}: {num}[src={h}]: {num} is not a numeral of {h}'s statement as CLAIMS.md prints it")
                    continue
                if not universal:
                    errs.append(f"FB2 {sec}: {num}[src{op}{h}]: {h} is not a universal statement; an existence "
                                f"statement refutes no printed value")
                    continue
                half = Fraction(1, 2) * Fraction(10) ** (-k)
                if op == ">":
                    ok = [x for x, (lo, hi) in q.items() if hi is not None and v - half >= hi]
                    if not ok:
                        errs.append(f"FB2 {sec}: {num}[src>{h}]: the rounding interval of {num} reaches below every upper "
                                    f"bound in the conclusion of {h} ({', '.join(f'{x} < {float(hi):.10g}' for x, (lo, hi) in q.items() if hi is not None) or 'none'}): "
                                    f"the certified statement does not show this printed value too large")
                else:
                    ok = [x for x, (lo, hi) in q.items() if lo is not None and v + half <= lo]
                    if not ok:
                        errs.append(f"FB2 {sec}: {num}[src<{h}]: the rounding interval of {num} reaches above every lower "
                                    f"bound in the conclusion of {h} ({', '.join(f'{float(lo):.10g} < {x}' for x, (lo, hi) in q.items() if lo is not None) or 'none'}): "
                                    f"the certified statement does not show this printed value too small")
            # FB4
            for w in WORDS.finditer(s):
                phrase = re.sub(r"\s+", " ", w.group(0).lower())
                if f"words {sec} {phrase}" not in baseline:
                    errs.append(f"FB4 {sec}: '{w.group(0)}': a spelled-out size in a verified finding; state sizes as "
                                f"certified numbers (generated block) or quote the source")
        # FB5
        for m in re.finditer(r"`(?:[A-Za-z0-9_.]*\.)?([A-Za-z0-9_]+)` \(", prose):
            h = m.group(1)
            if h not in cb:
                continue
            depth, i = 1, m.end()
            while i < len(prose) and depth:
                depth += {"(": 1, ")": -1}.get(prose[i], 0)
                i += 1
            par = prose[m.end():i - 1]
            universal, unique, then, q = bounds(cb[h])
            u = [x.group(0) for x in UNIQ.finditer(par)
                 if not re.search(r"(?i)\b(not|no|non)\W*$", par[:x.start()])]
            if u and not unique:
                errs.append(f"FB5 {sec}: `{h}` ({par[:60]}…) says '{u[0]}' but {h} states no uniqueness "
                            f"(no ∃!, no universal equation in its conclusion)")
            if not universal and UNIV.search(par) and not EXIST.search(par):
                errs.append(f"FB5 {sec}: `{h}` ({par[:60]}…) generalises ('{UNIV.search(par).group(0)}') over an "
                            f"existence statement without saying that something exists")
    return errs


CORRECT = re.compile(r"^- \*\*Correct\b.*$", re.M)  # "Correct" and "Correct (…)", not "Correction"
CERT_LINE = re.compile(r"^    - ([^:`]+): `(.+)` rounds to (\S+?)\[✓[^\]]*\] at (\d+) decimals?; role ([^.]+)\.$")
ROLE_WORD = {"printed": "printed value", "derived": "value derived in Lean", "free": "value of the free quantity"}


def sections_full(text):
    """{F<k>: whole section text, generated blocks included} of the verified-findings section."""
    i = text.find("\n## Verified findings")
    if i < 0:
        return {}
    j = text.find("\n## ", i + 1)
    scope = text[i:j if j >= 0 else len(text)]
    return {m.group(1): m.group(0) for m in re.finditer(r"^### (F\d+)\b(.*?)(?=^### |\Z)", scope, re.S | re.M)}


def split_top(expr):
    """`A - B` split at its one top-level binary minus, else None."""
    depth, cuts = 0, []
    for i, c in enumerate(expr):
        depth += {"(": 1, ")": -1}.get(c, 0)
        if depth == 0 and expr[i:i + 3] == " - ":
            cuts.append(i)
    return (expr[:cuts[0]], expr[cuts[0] + 3:]) if len(cuts) == 1 else None


def record_items(body):
    """[(record, quantifier line, [(kind, expr, value, k, role)])] of the generated blocks of a section body."""
    out = []
    for line in body.splitlines():
        m = re.match(r"^  - `Checked\.Records\.([A-Za-z0-9_]+)`, as Lean states it:$", line)
        if m:
            out.append([m.group(1), None, []])
            continue
        if out and out[-1][1] is None and line.startswith("    > **"):
            out[-1][1] = line
        m = CERT_LINE.match(line)
        if out and m:
            out[-1][2].append((m.group(1), m.group(2), m.group(3), int(m.group(4)), m.group(5)))
    return [tuple(x) for x in out]


def generated_correct(sec, body, cb, phrases):
    """The generated Correct line of section `sec` (None if it shows no record)."""
    clauses = []
    for rec, quant, items in record_items(body):
        q = quant or ""
        if "**For every**" in q:
            kind = "for every data meeting its hypotheses"
        elif "there is" in cb.get(rec, "").split("**It holds that**")[-1].split("\nwhere\n")[0]:
            kind = "there are data meeting its conditions"
        else:
            kind = "a statement about fixed values"
        cls = [ph for atom, ph in phrases if atom in cb.get(rec, "")]
        cls = list(dict.fromkeys(cls))
        head = f"`{rec}` ({kind}" + (f"; class: {', '.join(cls)}" if cls else "") + ")"
        facts = []
        for knd, expr, val, k, role in items:
            m = re.fullmatch(r"difference\((\w+)−(\w+)\)", role.strip())
            if not m:
                continue
            v, _ = prose_value(val)
            half = Fraction(1, 2) * Fraction(10) ** (-k)
            parts = split_top(expr)
            a = ROLE_WORD.get(m.group(1), m.group(1)) + (f" `{parts[0]}`" if parts else "")
            b = ROLE_WORD.get(m.group(2), m.group(2)) + (f" `{parts[1]}`" if parts else "")
            if v - half > 0:
                facts.append(f"the {a} lies above the {b}")
            elif v + half < 0:
                facts.append(f"the {a} lies below the {b}")
            else:
                facts.append(f"the sign of the {a} minus the {b} is not fixed by the certified rounding")
        clauses.append(head + ": " + ("; ".join(facts) + ", by the difference certified below" if facts
                                      else "the certified values below"))
    if not clauses:
        return None
    return (f"- **Correct (generated from the Lean records by `python3 scripts/trust/check_findings.py "
            f"--write-correct {sec}`; do not edit):** " + "; ".join(clauses) + ".")


def fb8(text, baseline):
    errs = []
    for sec, prose, records in verified_sections(text):
        own = [r for r in records if r.startswith(sec + "_")]
        if not own and f"norecord {sec}" not in baseline:
            errs.append(f"FB8 {sec}: a verified finding with no generated block of a record of its own ({sec}_…): "
                        f"a finding is verified by a Lean record in Checked/Records, not by prose citing theorems")
    return errs


def correct_lines(body):
    return [l.rstrip() for l in CORRECT.findall(re.sub(r"^<!-- certified:.*?^<!-- /certified -->$", "", body,
                                                        flags=re.S | re.M))]


def fb9(old, new, cb, phrases):
    """FB9: a new or changed Correct line must be the generated one."""
    a, b = sections_full(old), sections_full(new)
    errs = []
    for k in sorted(b, key=lambda x: int(x[1:])):
        if k in a and correct_lines(a[k]) == correct_lines(b[k]):
            continue
        g = generated_correct(k, b[k], cb, phrases)
        if g is None:
            errs.append(f"FB9 {k}: its Correct line is new or changed since BASE but the finding shows no record to "
                        f"generate it from: add the record first")
        elif correct_lines(b[k]) != [g]:
            errs.append(f"FB9 {k}: its Correct line is new or changed since BASE and is not the generated one; run "
                        f"`python3 scripts/trust/check_findings.py --write-correct {k}` (the line that states what is "
                        f"correct is generated from the records, never rewritten by hand)")
    return errs


def write_correct(text, secs, cb, phrases):
    full = sections_full(text)
    for k in secs:
        g = generated_correct(k, full[k], cb, phrases)
        assert g is not None, f"{k} shows no record"
        body = full[k]
        cl = CORRECT.findall(re.sub(r"^<!-- certified:.*?^<!-- /certified -->$", "", body, flags=re.S | re.M))
        if cl:
            nb = body.replace(cl[0], g, 1)
            for extra in cl[1:]:
                nb = nb.replace(extra + "\n", "", 1)
        else:  # after the heading's Printed line, else right after the heading
            lines = body.split("\n")
            at = next((i + 1 for i, l in enumerate(lines) if l.startswith("- **Printed")), 1)
            nb = "\n".join(lines[:at] + [g] + lines[at:])
        assert text.count(body) == 1
        text = text.replace(body, nb)
    return text


def section_prose(text):
    """{F<k>: prose with generated blocks removed and trailing blanks stripped} of the verified-findings section."""
    return {k: "\n".join(l.rstrip() for l in prose.strip().splitlines()) for k, prose, _ in verified_sections(text)}


def fb7(old, new, ledger_added):
    """FB7: changed, new or removed verified findings need a LEDGER line added since BASE naming FINDINGS.md and `F<k>`."""
    a, b = section_prose(old), section_prose(new)
    errs = []
    for k in sorted(set(a) | set(b), key=lambda x: int(x[1:])):
        if a.get(k) == b.get(k):
            continue
        what = "new" if k not in a else ("removed" if k not in b else "changed")
        if not any("FINDINGS.md" in l and re.search(r"`" + k + r"`", l) for l in ledger_added):
            errs.append(f"FB7: verified finding {k} is {what} since BASE (prose outside the generated blocks) and no "
                        f"line added to LEDGER.md names `FINDINGS.md` and `{k}`: a finding's words change only disclosed")
    return errs


def ledger_added_lines(base):
    out = subprocess.run(["git", "diff", "--unified=0", base, "--", "LEDGER.md"], capture_output=True, text=True).stdout
    return [l[1:] for l in out.splitlines() if l.startswith("+") and not l.startswith("+++")]


def selftest():
    claims = ("## `W`\n\nFull name `X.W`.\n\n**For every** `q : ℝ`:\n\n**assuming**\n\n1. `0 < q`\n\n**then**\n\n"
              "1. `52181e-7 < q`\n2. `q < 52182e-7`\n\nAuthor's paraphrase\n\n"
              "## `E`\n\nFull name `X.E`.\n\n**It holds that**\n\n- there is `q` such that `q < 1`\n\n"
              "## `F9_r`\n\nFull name `X.F9_r`.\n\n**For every** `q : ℝ`:\n\n**then**\n\n- `RoundsTo (q - -1988 / 10000) 1e-6 6`\n\n"
              "where\n\n- *pr* — PRINTED: is defined as *5221e-6*\n")
    head = "# x\n\n## Verified findings\n\n"
    tail = "\n## Candidates under verification\n"
    good = (head + "### F9 (x). Paper: values at β = −0.1988[src=F9_r] too large\n- **Printed:** 0.005221[src>W], "
            "0.005221[src=F9_r]; window `W` (the wall shear of every such solution lies in it); `E` (there is one; all "
            "of them non-unique)\n- **Correct:** too large in the decay class\n- **Referee:** quotes 0.005226[src]\n<!-- certified: F9_r -->\n- block\n<!-- /certified -->\n" + tail)
    bad = [
        ("FB1", good.replace("<!-- certified: F9_r -->", "<!-- certified: F8_r -->")),
        ("FB2", good.replace("0.005221[src>W]", "0.005218[src>W]")),          # inside the rounding: not refuted
        ("FB2", good.replace("−0.1988[src=F9_r]", "−0.1998[src=F9_r]")),      # not a numeral of the record
        ("FB2", good.replace("0.005221[src>W]", "0.005221[src>E]")),          # existential refutes nothing
        ("FB2", good.replace("0.005221[src>W]", "0.005221[src<W]")),          # wrong side
        ("FB3", good.replace("0.005221[src>W]", "0.005226[src]")),
        ("FB3", good.replace("\n<!-- certified: F9_r", "\n- **Correct:** also 0.005226[src]\n<!-- certified: F9_r")),
        ("FB4", good.replace("too large", "three units too large")),
        ("FB6", good.replace("too large in the decay class", "too large")),
        ("FB5", good.replace("(there is one; all of them non-unique)", "(the solution is unique)")),
        ("FB5", good.replace("(there is one; all of them non-unique)", "(all solutions lie below)")),
    ]
    fails = 0
    ph = [("RoundsTo (q", "decay class")]
    e = check(good, claims, set(), ph)
    if e:
        print("selftest: clean control fails:", e)
        fails += 1
    for rule, txt in bad:
        e = check(txt, claims, set(), ph)
        if not any(x.startswith(rule) for x in e):
            print(f"selftest: {rule} control not rejected; errors: {e}")
            fails += 1
    # FB7 controls (diff rule): a reworded Scope line, a new finding, a removed one; clean twins: disclosed, or only
    # the generated block changed.
    led = ["- x — FINDINGS.md `F9` Scope reworded"]
    fb7_bad = [(good, good.replace("too large in the decay class", "too large in every class"), []),
               (good, good.replace(tail, "### F10 (y). new\n- **Correct:** z\n" + tail), led),
               (good, head + tail, [])]
    fb7_ok = [(good, good.replace("too large in the decay class", "too large in every class"), led),
              (good, good.replace("- block\n", "- other block\n"), []), (good, good, [])]
    for o, n, l in fb7_bad:
        if not any(x.startswith("FB7") for x in fb7(o, n, l)):
            print("selftest: FB7 control not rejected")
            fails += 1
    for o, n, l in fb7_ok:
        if fb7(o, n, l):
            print("selftest: FB7 clean twin rejected:", fb7(o, n, l))
            fails += 1
    # FB8 / FB9 controls (run 2026-11-13T1028Z, round AK): a new finding without a record of its own; a hand-written
    # or flipped Correct line on a changed finding; clean twins: baselined legacy finding, generated line, unchanged line.
    blk = ("<!-- certified: F9_r -->\n  - `Checked.Records.F9_r`, as Lean states it:\n    > **For every** `q : ℝ`:\n"
           "    - difference: `pr - q 0` rounds to 0.000003[✓F9_r(difference)] at 6 decimals; role difference(printed−free).\n"
           "<!-- /certified -->\n")
    base9 = good.replace("<!-- certified: F9_r -->\n- block\n<!-- /certified -->\n", blk)
    gen = generated_correct("F9", sections_full(base9)["F9"], claims_blocks(claims), ph)
    if not gen or "printed value `pr` lies above the value of the free quantity `q 0`" not in gen or "decay class" not in gen:
        print("selftest: FB9 generator wrong:", gen)
        fails += 1
    new9 = write_correct(base9, ["F9"], claims_blocks(claims), ph)
    flip = new9.replace("lies above", "lies below")
    hand = base9.replace("- **Correct:** too large in the decay class", "- **Correct:** too large by 3 units, decay class")
    f15 = base9.replace(tail, "### F15 (y). new finding\n- **Correct:** z\n" + tail)
    fb8_9 = [("FB8", fb8(f15, set())), ("FB9", fb9(base9, flip, claims_blocks(claims), ph)),
             ("FB9", fb9(base9, hand, claims_blocks(claims), ph)), ("FB9", fb9(base9, f15, claims_blocks(claims), ph))]
    for rule, e in fb8_9:
        if not any(x.startswith(rule) for x in e):
            print(f"selftest: {rule} control not rejected")
            fails += 1
    for e in [fb8(f15, {"norecord F15"}), fb8(base9, set()), fb9(base9, new9, claims_blocks(claims), ph),
              fb9(base9, base9.replace("- **Referee:**", "- **Referee (re-read):**"), claims_blocks(claims), ph)]:
        if e:
            print("selftest: FB8/FB9 clean twin rejected:", e)
            fails += 1
    print(f"check_findings selftest: {len(bad) + 1 + len(fb7_bad) + len(fb7_ok) + 1 + len(fb8_9) + 4} controls, {fails} failing")
    return fails == 0


def main():
    args = sys.argv[1:]
    if not selftest():
        sys.exit(1)
    if args == ["--selftest"]:
        return
    findings = open(FINDINGS, encoding="utf-8").read()
    claims = open(CLAIMS, encoding="utf-8").read()
    if args and args[0] == "--write-correct":
        out = write_correct(findings, args[1:], claims_blocks(claims), load_phrases())
        open(FINDINGS, "w", encoding="utf-8").write(out)
        print(f"check_findings: Correct line generated for {', '.join(args[1:])}")
        return
    baseline = load_baseline()
    norec = load_baseline(NORECORD)
    errs = check(findings, claims, baseline, load_phrases()) + fb8(findings, norec)
    if "--base" in args:
        base = args[args.index("--base") + 1]
        try:
            old = subprocess.run(["git", "show", f"{base}:{BASELINE}"], capture_output=True, text=True, check=True).stdout
            grown = sorted(baseline - load_baseline(text=old))
        except subprocess.CalledProcessError:
            grown = []  # the baseline is new since BASE (introduced with this check)
        for g in grown:
            errs.append(f"FB-base: {BASELINE} gained '{g}' since {base}: the baseline only shrinks")
        try:
            oldp = subprocess.run(["git", "show", f"{base}:{PHRASES}"], capture_output=True, text=True, check=True).stdout
            lost = sorted(set(load_phrases(text=oldp)) - set(load_phrases()))
        except subprocess.CalledProcessError:
            lost = []
        for a, b in lost:
            errs.append(f"FB-base: {PHRASES} lost '{a} => {b}' since {base}: the registry only grows")
        try:
            oldf = subprocess.run(["git", "show", f"{base}:{FINDINGS}"], capture_output=True, text=True, check=True).stdout
            errs += fb7(oldf, findings, ledger_added_lines(base))
            errs += fb9(oldf, findings, claims_blocks(claims), load_phrases())
        except subprocess.CalledProcessError:
            errs.append(f"FB7: cannot read {FINDINGS} at {base}")
        try:
            oldn = subprocess.run(["git", "show", f"{base}:{NORECORD}"], capture_output=True, text=True, check=True).stdout
            for g in sorted(norec - load_baseline(text=oldn)):
                errs.append(f"FB-base: {NORECORD} gained '{g}' since {base}: the baseline only shrinks")
        except subprocess.CalledProcessError:
            pass  # introduced with FB8 (run 2026-11-13T1028Z)
    for e in errs:
        print("::error::" + e)
    print(f"check_findings: {len(verified_sections(findings))} verified findings, {len(errs)} problems")
    sys.exit(1 if errs else 0)


if __name__ == "__main__":
    main()
