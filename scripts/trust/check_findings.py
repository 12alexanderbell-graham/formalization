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
  FB3  in a section with a generated block, a bare `[src]` decimal is an error unless listed in the shrink-only
       baseline `scripts/trust/findings_baseline.txt` (`src <section> <value>`): a printed value the finding relies on
       is bound by FB2 or visibly unbound (d01, d05).
  FB4  a spelled-out count next to a unit of size ("three units", "seven decimals", "fourth significant digit") is
       an error unless baselined (`words <section> <phrase>`): sizes are certified numbers in generated blocks (d06).
  FB5  a parenthetical right after a cited headline, `` `H` (…) ``, that calls something unique (unique…, "the only",
       "exactly one", "at most one"; not "non-unique…" or "not unique") needs H to state uniqueness (`∃!`, or a
       universal statement with an equation and no `≠` in its conclusion); one that generalises (every, any, all,
       each, whatever) over an existential H must also say that something exists (d03; the shape rule of
       check_prose.py applied to the words that describe a cited theorem in a finding).

Open (recorded, not checked): which solution class the "Correct" line names (d02: a qualifier dropped from prose
while the record keeps it as a hypothesis; the generated block under it quotes every hypothesis).

  python3 scripts/trust/check_findings.py              rules FB1–FB5 on FINDINGS.md (reads CLAIMS.md)
  python3 scripts/trust/check_findings.py --base SHA   also: the baseline gained no line since SHA
  python3 scripts/trust/check_findings.py --selftest   controls only
"""
import re
import subprocess
import sys
from fractions import Fraction

FINDINGS = "FINDINGS.md"
CLAIMS = "CLAIMS.md"
BASELINE = "scripts/trust/findings_baseline.txt"
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


def check(findings, claims, baseline):
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
        cited = set(re.findall(r"`(?:[A-Za-z0-9_.]*\.)?([A-Za-z0-9_]+)`", prose)) | set(records)
        for line in prose.split("\n"):
            claimline = line.startswith("### ") or line.startswith("- **Printed")
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
            "of them non-unique)\n<!-- certified: F9_r -->\n- block\n<!-- /certified -->\n" + tail)
    bad = [
        ("FB1", good.replace("<!-- certified: F9_r -->", "<!-- certified: F8_r -->")),
        ("FB2", good.replace("0.005221[src>W]", "0.005218[src>W]")),          # inside the rounding: not refuted
        ("FB2", good.replace("−0.1988[src=F9_r]", "−0.1998[src=F9_r]")),      # not a numeral of the record
        ("FB2", good.replace("0.005221[src>W]", "0.005221[src>E]")),          # existential refutes nothing
        ("FB2", good.replace("0.005221[src>W]", "0.005221[src<W]")),          # wrong side
        ("FB3", good.replace("0.005221[src>W]", "0.005226[src]")),
        ("FB4", good.replace("too large", "three units too large")),
        ("FB5", good.replace("(there is one; all of them non-unique)", "(the solution is unique)")),
        ("FB5", good.replace("(there is one; all of them non-unique)", "(all solutions lie below)")),
    ]
    fails = 0
    e = check(good, claims, set())
    if e:
        print("selftest: clean control fails:", e)
        fails += 1
    for rule, txt in bad:
        e = check(txt, claims, set())
        if not any(x.startswith(rule) for x in e):
            print(f"selftest: {rule} control not rejected; errors: {e}")
            fails += 1
    print(f"check_findings selftest: {len(bad) + 1} controls, {fails} failing")
    return fails == 0


def main():
    args = sys.argv[1:]
    if not selftest():
        sys.exit(1)
    if args == ["--selftest"]:
        return
    findings = open(FINDINGS, encoding="utf-8").read()
    claims = open(CLAIMS, encoding="utf-8").read()
    baseline = load_baseline()
    errs = check(findings, claims, baseline)
    if "--base" in args:
        base = args[args.index("--base") + 1]
        try:
            old = subprocess.run(["git", "show", f"{base}:{BASELINE}"], capture_output=True, text=True, check=True).stdout
            grown = sorted(baseline - load_baseline(text=old))
        except subprocess.CalledProcessError:
            grown = []  # the baseline is new since BASE (introduced with this check)
        for g in grown:
            errs.append(f"FB-base: {BASELINE} gained '{g}' since {base}: the baseline only shrinks")
    for e in errs:
        print("::error::" + e)
    print(f"check_findings: {len(verified_sections(findings))} verified findings, {len(errs)} problems")
    sys.exit(1 if errs else 0)


if __name__ == "__main__":
    main()
