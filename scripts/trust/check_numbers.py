#!/usr/bin/env python3
"""Certified numbers in the records (trust track T4/T5, run 2026-10-31T0228Z). Blocking in CI.

Red-team defects A06 and B07 (run 2026-10-31T0028Z) changed numbers in FINDINGS.md and every
check accepted them. Rule: every number in the "Verified findings" section of FINDINGS.md that
is a decimal (or follows ≈/≃) carries a tag right after it:

  [✓name]  certified: `Checked.Records.name` is a registered headline whose statement contains
           `RoundsTo x d k` with `d` written with `k` decimals exactly as in the prose
           (literals extracted by scripts/trust/StatementDeps.lean into .lake/records_numbers.tsv);
  [in✓name] an input (parameter value) at which the record `name` is stated: the value must be one
           of the rational numerals in its statement (red team D, defect D02 changed Ω_m = 0.3 to 0.7
           next to certified values computed at 0.3). In a sentence (split at ". " and "; ") that
           contains a certified number, bare [in] and [src] are errors;
  [src]    quoted from the source (a number printed in the paper);
  [in]     an input chosen for illustration (a parameter value), not a result;
  [unc]    computed but NOT machine-checked (the reader sees that it is unchecked).

Selectors (run 2026-11-08T0028Z; blind red team T, defect d01 swapped the redshifts of the two
certified Milne percentages of F8 and every check accepted it — a record certified *values*, not the
argument the prose attached to them). StatementDeps.lean writes, for every certified value, the
*selector* of the certified quantity `x` of `RoundsTo x d k`: `@Def` when x's head is a program
definition, and `v=p/q` for each rational numeral argument of that definition (binder `v`) or of a
`fun`, and for each `let v := p/q` in x. A tag may carry it, `0.56[✓F8_sizes(z=1)]`,
`−0.249[✓F10_eta(correct20, Ω=0.041)]` (values compared exactly):
  S1  a tag's selector, if given, must equal the selector of a conjunct certifying that number;
  S2  a tag of a record with several certified values must identify exactly one conjunct by its
      selector (an absent selector is the empty one), unless the record is in the shrink-only
      `scripts/trust/records_selector_baseline.txt` (records whose conjuncts have equal selectors);
  S3  in a sentence, a phrase `v = c` (prose, any tag) where `v` is bound by some selector tag of the
      sentence must agree with the nearest such tag before it (else the nearest after it): the
      argument the prose names is the argument the record evaluates at;
  S4  in such a sentence an untagged numeral equal to an argument value of a selector tag is an error
      unless it is the `c` of an S3 phrase `v = c` ("at redshift 2" must be "at z = 2").
  P1  an input tag may name the parameter slot it fills, `0.245[in✓F2_toy(Ω)]`: the record must fix that
      parameter (binder of a program definition, or a `let` of a certified quantity) to that value;
  P2  an input tag of a record that fixes several parameters must name its slot (adversary of run
      2026-11-08T0028Z, d3: the toy parameters (w₀, wₐ) permuted in prose passed set membership).
`--selftest` runs a rejecting control and a clean twin for S1–S3 (also run first by every check).

With `--base REF` (CI, after the frozen-registry check) it also compares with REF: a certified
pair (number, [✓name]) present at REF and absent now (number changed, or tag downgraded to
[src]/[in]/[unc]) needs a LEDGER.md line added since REF naming `name` (as frozen entries do).

Scope: the whole of FINDINGS.md except the section "## Candidates under verification" (which is
labelled UNVERIFIED as a whole); a new heading does not end the scope (red team D, defect D06).
Signs: hyphen, minus sign, en dash and other dashes all count as a minus (D07). A number written
with a power of ten, `1.3×10⁻⁵`, is one token whose value must equal the certified literal (D03).

Not numbers for this rule: arXiv identifiers, equation numbers in parentheses "(10.54)",
anything inside `code`. Run after StatementDeps.lean (which writes the .tsv).
"""
import re
import subprocess
import sys
from decimal import Decimal
from fractions import Fraction

FINDINGS = "FINDINGS.md"
TSV = ".lake/records_numbers.tsv"
UNVERIFIED = "## Candidates under verification"

DASHES = "−–—‐‑‒-"
SUP = "⁰¹²³⁴⁵⁶⁷⁸⁹"
NUM = r"[" + DASHES + r"]?\d+(?:\.\d+)?(?:×10[⁻⁺]?[" + SUP + r"]+)?"
SELX = r"(?:\([^()\[\]]*\))?"
TAG = r"\[(✓[A-Za-z0-9_]+" + SELX + r"|in✓[A-Za-z0-9_]+" + SELX + r"|src|in|unc)\]"
SELBASE = "scripts/trust/records_selector_baseline.txt"
PARAMS = ".lake/records_params.tsv"
try:
    CITATIONS = {l.strip() for l in open(__import__("pathlib").Path(__file__).resolve().parent / "citations.txt", encoding="utf-8")
                 if l.strip() and not l.startswith("#")}
except FileNotFoundError:
    CITATIONS = set()


def norm(s):
    for d in DASHES:
        s = s.replace(d, "-")
    return s


def value(tok):
    """(exact value, number of decimals) of a prose number or a certified literal."""
    tok = norm(tok)
    exp = 0
    if "×10" in tok:
        tok, e = tok.split("×10")
        e = e.replace("⁻", "-").replace("⁺", "")
        exp = int("".join(str(SUP.index(c)) if c in SUP else c for c in e))
    dec = len(tok.split(".")[1]) if "." in tok else 0
    return Decimal(tok).scaleb(exp), max(dec - exp, 0)


GENERATED = "## Certified numbers (generated from the Lean records; do not edit)"


def scope(text):
    g = text.find("\n" + GENERATED)
    if g >= 0:
        k = text.find("\n## ", g + 1)
        text = text[:g] + ("\n" + text[k:] if k >= 0 else "\n")
    i = text.find("\n" + UNVERIFIED)
    if i < 0:
        return text
    j = text.find("\n## ", i + 1)
    return text[:i] + ("\n" + text[j:] if j >= 0 else "")


def sel_tag_text(col):
    """the tag form of a .tsv selector: `@printedD4;Ω=41/1000` -> `printedD4, Ω=0.041`"""
    head, binds = parse_sel_tsv(col)
    def dec(x):
        if x.denominator == 1:
            return str(x.numerator).replace("-", "−")
        d = Decimal(x.numerator) / Decimal(x.denominator)
        return (format(d.normalize(), "f") if d == Decimal(x.numerator) / Decimal(x.denominator) else str(x)).replace("-", "−")
    order = [it.split("=")[0] for it in col.split(";") if "=" in it]
    items = ([head] if head else []) + [f"{v}={dec(dict(binds)[v])}" for v in order]
    return ", ".join(items)


def generated_table(rows):
    """FINDINGS.md's generated section: every certified value with the tag that selects it and the quantity
    as Lean states it (run 2026-11-08T0028Z: the binding of a number to its quantity is read from Lean, not
    from prose)."""
    out = [GENERATED, "",
           "Generated by `scripts/trust/check_numbers.py --write` from `.lake/records_numbers.tsv` (written by "
           "`scripts/trust/StatementDeps.lean` from the statements of the `Checked.Records` headlines); CI fails if "
           "it is stale. Each row: the tag that selects the value (the selector in parentheses is required when a "
           "record certifies several values), the certified decimal, and the quantity Lean certifies it for "
           "(`RoundsTo x d k`: |x − d| ≤ 10⁻ᵏ/2). Free names (`a`, `t₀`, `r`) are bound in the record's statement; "
           "read the full statement in CLAIMS.md.", "",
           "| tag | value | certified quantity |", "|---|---|---|"]
    for r in rows:
        name, val = r[0], r[1]
        sel = r[2] if len(r) > 2 else ""
        x = r[3] if len(r) > 3 else ""
        st = sel_tag_text(sel)
        tag = f"✓{name}" + (f"({st})" if st else "")
        out.append(f"| {tag} | {val.replace('-', '−')} | `{x.replace('|', '∣')}` |")
    return "\n".join(out) + "\n"


CODE_OK = re.compile(r"`(?:[A-Za-z_][\w.'⁰¹²³⁴⁵⁶⁷⁸⁹]*|[\w.\-/]+\.(?:png|pdf|md|lean|py|txt|sh|json|tsv))`$")


def code_blank(line):
    """Code spans that name a constant or a file are not read as numbers. Since run 2026-11-04T0428Z
    every other code span is read like prose (red team F, defect F05: a wrong decimal `2.76` placed in
    a code span escaped the check)."""
    return re.sub(r"`[^`]*`", lambda mm: " " * len(mm.group()) if CODE_OK.match(mm.group()) else
                  " " + mm.group()[1:-1] + " ", line)


def certified_pairs(text):
    out = {}
    for line in scope(text).split("\n"):
        for t in re.finditer(r"(" + NUM + r")\[((?:in)?✓[A-Za-z0-9_]+" + SELX + r")\]", code_blank(line)):
            k = (norm(t.group(1)), t.group(2))
            out[k] = out.get(k, 0) + 1
    return out


def base_check(base):
    # a new branch has no "before" commit (all zeros): compare with the parent, as check_relock.py does
    if not base or set(base) == {"0"} or subprocess.run(
            ["git", "cat-file", "-e", base + "^{commit}"], capture_output=True).returncode:
        base = "HEAD~1"
    # S2's baseline only shrinks (run 2026-11-08T0028Z)
    oldb = subprocess.run(["git", "show", f"{base}:{SELBASE}"], capture_output=True, text=True)
    oldset = {l.split("#")[0].strip() for l in oldb.stdout.splitlines() if l.split("#")[0].strip()} if oldb.returncode == 0 else None
    try:
        newset = {l.split("#")[0].strip() for l in open(SELBASE, encoding="utf-8") if l.split("#")[0].strip()}
    except FileNotFoundError:
        newset = set()
    grown = sorted(newset - oldset) if oldset is not None else []
    for g in grown:
        print(f"::error::S2: {SELBASE} gained {g} against {base} (it may only shrink)")
    if grown:
        return 1
    old = subprocess.run(["git", "show", f"{base}:{FINDINGS}"], capture_output=True, text=True)
    if old.returncode != 0:
        print(f"certified-number diff: no {FINDINGS} at {base}; skipped")
        return 0
    before = certified_pairs(old.stdout)
    after = certified_pairs(open(FINDINGS, encoding="utf-8").read())
    lost = [k for k, c in before.items() if after.get(k, 0) < c]
    led = subprocess.run(["git", "diff", base, "HEAD", "--", "LEDGER.md"], capture_output=True, text=True).stdout
    added = "\n".join(l[1:] for l in led.splitlines() if l.startswith("+") and not l.startswith("+++"))
    missing = [k for k in lost if not re.search(r"(?<![\w.])" + re.escape(k[1].split("✓")[-1].split("(")[0]) + r"(?![\w])", added)]
    print(f"certified-number diff vs {base}: {len(before)} certified pairs before, {len(after)} now, "
          f"{len(lost)} removed or changed")
    for num, name in missing:
        name = name.replace("in✓", "").replace("✓", "").split("(")[0]
        print(f"::error::certified number {num}[✓{name}] was changed, removed or downgraded without a "
              f"LEDGER.md entry naming {name}")
    return 1 if missing else 0


def parse_sel_tsv(col):
    """selector column of records_numbers.tsv: `@Def;v=p/q;...` -> (head, frozenset((v, Fraction)))"""
    head, binds = "", set()
    for it in [x for x in col.split(";") if x]:
        if it.startswith("@"):
            head = it[1:]
        elif "=" in it:
            v, _, fr = it.partition("=")
            binds.add((v, Fraction(fr)))
    return head, frozenset(binds)


def parse_sel_tag(txt):
    """selector written in a tag: `(Def, v=0.041)` -> (head, frozenset) or an error string"""
    head, binds = "", set()
    for it in [x.strip() for x in txt.split(",") if x.strip()]:
        if "=" in it:
            v, _, num = it.partition("=")
            v, num = v.strip(), num.strip()
            if not re.fullmatch(NUM, num):
                return f"selector item {it!r}: not `name=number`"
            binds.add((v, Fraction(value(num)[0])))
        elif re.fullmatch(r"[^\W\d][\w'₀-₉]*", it):
            if head:
                return f"selector {txt!r} names two definitions"
            head = it
        else:
            return f"selector item {it!r}: not a definition name or `name=number`"
    return head, frozenset(binds)


def fmt_sel(sel):
    head, binds = sel
    items = ([head] if head else []) + [f"{v}={str(x) if x.denominator != 1 else x.numerator}" for v, x in sorted(binds, key=str)]
    return "(" + ", ".join(items) + ")" if items else "(no selector)"


def check_text(text, cert, params, ambig_ok, fixed=None):
    """All FINDINGS rules on `text`. cert: name -> [(value string, selector)]. Returns (errors, counts)."""
    errors, counts = [], {"✓": 0, "src": 0, "in": 0, "unc": 0}
    fixed = fixed or {}
    for line in scope(text).split("\n"):
        s = code_blank(line)
        tagged_starts = set()
        bound_tags = []   # (start, end, {var: Fraction}) of selector tags with bindings (rule S3)
        for t in re.finditer(r"(" + NUM + r")" + TAG, s):
            num, tag = t.group(1), t.group(2)
            tagged_starts.add(t.start(1))
            if tag.startswith("in✓"):
                m = re.fullmatch(r"in✓([A-Za-z0-9_]+)(?:\(([^()]*)\))?", tag)
                name, slot = m.group(1), m.group(2)
                v, _ = value(num)
                slots = fixed.get(name, {})
                if Fraction(v) not in params.get(name, set()):
                    errors.append(f"{num}[{tag}]: {name} is not stated at {num} (its parameters: "
                                  f"{sorted(str(x) for x in params.get(name, set()))[:12]})")
                elif slot is not None and Fraction(v) not in slots.get(slot.strip(), set()):
                    errors.append(f"P1: {num}[{tag}]: {name} does not fix the parameter {slot.strip()} to {num} "
                                  f"(its fixed parameters: {', '.join(f'{k}={sorted(str(x) for x in vs)}' for k, vs in sorted(slots.items()))})")
                elif slot is None and len(slots) > 1:
                    errors.append(f"P2: {num}[{tag}]: {name} fixes several parameters "
                                  f"({', '.join(sorted(slots))}); name the one this value is: "
                                  f"{num}[in✓{name}({'|'.join(sorted(k for k, vs in slots.items() if Fraction(v) in vs)) or '?'})]")
                else:
                    counts["in"] += 1
            elif tag.startswith("✓"):
                m = re.fullmatch(r"✓([A-Za-z0-9_]+)(?:\((.*)\))?", tag)
                name, seltxt = m.group(1), m.group(2)
                if name not in cert:
                    errors.append(f"[✓{name}] after {num}: no registered Checked.Records headline {name} asserts a RoundsTo")
                    continue
                sel = None
                if seltxt is not None:
                    sel = parse_sel_tag(seltxt)
                    if isinstance(sel, str):
                        errors.append(f"{num}[{tag}]: {sel}")
                        continue
                    if sel[1]:
                        bound_tags.append((t.start(1), t.end(), dict(sel[1])))
                vals = [v for v, _ in cert[name]]
                if value(num) not in [value(v) for v in vals]:
                    errors.append(f"{num}[✓{name}]: {name} certifies {vals}, not {num}")
                    continue
                want = sel if sel is not None else ("", frozenset())
                same = [(v, c) for v, c in cert[name] if c == want]
                if sel is not None and not any(value(v) == value(num) for v, _ in same):
                    errors.append(f"S1: {num}[{tag}]: {name} certifies {num} with selector "
                                  f"{', '.join(fmt_sel(c) for v, c in cert[name] if value(v) == value(num))}, "
                                  f"not {fmt_sel(want)}")
                    continue
                if len(cert[name]) > 1 and name not in ambig_ok and len(same) != 1:
                    errors.append(f"S2: {num}[{tag}]: {name} certifies several values; the tag must name the selector "
                                  f"of this one: {', '.join(fmt_sel(c) for v, c in cert[name] if value(v) == value(num))}")
                    continue
                counts["✓"] += 1
            else:
                counts[tag] += 1
        for t in re.finditer(r"\[(✓[^\]]*|src|in|unc)\]×10", s):
            errors.append(f"power of ten after the tag {t.group()[:-3]}: write it before the tag, 1.3×10⁻⁵[✓name]")
        # an input in a sentence with a certified number must be bound to a record (red team D, D02)
        for sent in re.split(r"(?<=[.;])\s", s):
            if "[✓" in sent and ("[in]" in sent or "[src]" in sent or "[unc]" in sent):
                errors.append(f"bare [in]/[src]/[unc] in a sentence with a certified number: bind the parameter to "
                              f"its record, 0.3[in✓name], or move the quote to its own sentence: {sent.strip()[:90]}")
        # S3: an argument the prose names agrees with the selector of the certified value it describes
        off = 0
        for sent in re.split(r"(?<=[.;])\s", s):
            a0 = s.find(sent, off)
            off = a0 + len(sent)
            tags = [(a - a0, b - a0, bd) for a, b, bd in bound_tags if a0 <= a < off]
            vars_ = {v for _, _, bd in tags for v in bd}
            for v in vars_:
                for m in re.finditer(r"(?<![\w])" + re.escape(v) + r"\s*=\s*(" + NUM + r")", sent):
                    if any(a <= m.start() < b for a, b, _ in tags):
                        continue  # inside a tag
                    before = [t for t in tags if v in t[2] and t[1] <= m.start()]
                    after = [t for t in tags if v in t[2] and t[0] >= m.end()]
                    ref = before[-1] if before else (after[0] if after else None)
                    if ref and Fraction(value(m.group(1))[0]) != ref[2][v]:
                        errors.append(f"S3: prose `{m.group().strip()}` next to a certified value whose record evaluates at "
                                      f"{v} = {ref[2][v]}: …{sent[max(0, m.start() - 60):m.end() + 10].strip()}…")
            # S4: an argument value of a selector tag is stated in prose only in the checked form `v = c`
            # (adversary of run 2026-11-08T0028Z, d4: "at redshift 2 … at redshift 1" swapped the Milne
            # redshifts again past S3's pattern); untagged numerals only ([in✓…] tags: open, see LEDGER)
            bvals = {(v, x) for _, _, bd in tags for v, x in bd.items()}
            s3_spans = [m.span(1) for v in vars_ for m in re.finditer(
                r"(?<![\w])" + re.escape(v) + r"\s*=\s*(" + NUM + r")", sent)]
            for m in re.finditer(r"(?<![\w.⁰¹²³⁴⁵⁶⁷⁸⁹/^])(" + NUM + r")(?![\d\[])(?!\.\d)(?![⁰¹²³⁴⁵⁶⁷⁸⁹/])", sent):
                a, b = m.span(1)
                if any(x <= a < y for x, y, _ in tags) or (a, b) in s3_spans:
                    continue
                if sent[b:b + 1] == "[":
                    continue  # tagged
                fx = Fraction(value(m.group(1))[0])
                hit = sorted(v for v, x in bvals if x == fx)
                if hit:
                    errors.append(f"S4: bare {m.group(1)} in a sentence whose certified value is evaluated at "
                                  f"{hit[0]} = {m.group(1)}: write the argument as `{hit[0]} = {m.group(1)}` (checked by S3) "
                                  f"or only in the tag's selector: …{sent[max(0, a - 50):b + 10].strip()}…")
        for t in re.finditer(r"\[(✓[^\]]*|in✓[^\]]*|src|in|unc)\]", s):
            if not any(re.match(NUM + r"$", s[a:t.start()]) for a in tagged_starts if a < t.start()):
                errors.append(f"tag {t.group()} not directly after a number: {line.strip()[:80]}")
        # a selector's arguments are read by S1/S3, not as prose numbers
        s_num = re.sub(r"\[(?:in)?✓[A-Za-z0-9_]+\([^()\[\]]*\)\]", lambda mm: " " * len(mm.group()), s)
        for t in re.finditer(r"(?<![\w.])(" + NUM + r")(?!\d)(?!\.\d)", s_num):
            a, b = t.span(1)
            num = t.group(1)
            is_dec = "." in num or "×10" in num
            approx = s[:a].rstrip().endswith(("≈", "≃"))
            if not (is_dec or approx) or a in tagged_starts:
                continue
            if re.fullmatch(r"\d{4}\.\d{4,5}", num):
                continue  # arXiv identifier
            if s[a - 1:a] == "(" and s[b:b + 1] == ")":
                # an equation number, but only a registered one (run 2026-11-04T1028Z, red team G d08: a wrong
                # table value written "(2.77)" passed as a citation); registry shared with check_prose.py
                if num in CITATIONS:
                    continue
                errors.append(f"number in parentheses {num} is not a registered equation number "
                              f"(scripts/trust/citations.txt; tag it if it is a value): …{s[max(0, a - 50):b + 15].strip()}…")
                continue
            errors.append(f"untagged number {num}: …{s[max(0, a - 50):b + 15].strip()}…")
    return errors, counts


def selftest():
    """Controls for S1–S3 (a rule that rejects nothing fails CI; run 2026-11-07T1428Z practice)."""
    cert = {"R": [("0.56", parse_sel_tsv("z=1/1")), ("6.7", parse_sel_tsv("z=2/1"))],
            "Q": [("0.2153", parse_sel_tsv("@correctD4")), ("0.4555", parse_sel_tsv("@printedD4"))]}
    params = {"R": {Fraction(1), Fraction(2)}}
    fixed = {"T": {"w0": {Fraction(-93, 100)}, "wa": {Fraction(-41, 100)}}}
    params["T"] = {Fraction(-93, 100), Fraction(-41, 100)}
    cert["T"] = [("0.809", ("", frozenset()))]
    head = "## Verified findings\n"
    cases = [  # (text, rule that must fire, or None for a clean twin)
        ("(0.56[✓R(z=1)] % at z = 1, 6.7[✓R(z=2)] % at z = 2).", None),
        ("(6.7[✓R(z=2)] % at z = 1, 0.56[✓R(z=1)] % at z = 2).", "S3"),
        ("(6.7[✓R(z=1)] % at z = 1, 0.56[✓R(z=2)] % at z = 2).", "S1"),
        ("(0.56[✓R] % at z = 1, 6.7[✓R] % at z = 2).", "S2"),
        ("(0.56[✓R(z=1)] % at redshift 2, 6.7[✓R(z=2)] % at redshift 1).", "S4"),
        ("(0.56[✓R(z=1)] % and 6.7[✓R(z=2)] % of the series k²z⁴/120).", None),
        ("correct 0.2153[✓Q(correctD4)] vs printed 0.4555[✓Q(printedD4)].", None),
        ("correct 0.4555[✓Q(correctD4)] vs printed 0.2153[✓Q(printedD4)].", "S1"),
        ("toy (−0.93[in✓T(w0)], −0.41[in✓T(wa)]): 0.809[✓T].", None),
        ("toy (−0.41[in✓T(w0)], −0.93[in✓T(wa)]): 0.809[✓T].", "P1"),
        ("toy (−0.41[in✓T], −0.93[in✓T]): 0.809[✓T].", "P2"),
    ]
    bad = []
    for text, rule in cases:
        errs, _ = check_text(head + text + "\n", cert, params, set(), fixed)
        fired = {e.split(":")[0] for e in errs}
        if rule is None and errs:
            bad.append(f"clean control rejected: {text} -> {errs}")
        if rule is not None and rule not in fired:
            bad.append(f"control for {rule} not rejected: {text} -> {errs}")
    for b in bad:
        print(f"::error::check_numbers selftest: {b}")
    print(f"check_numbers selftest: {len(cases)} controls, {len(bad)} failing")
    return 1 if bad else 0


def main():
    if len(sys.argv) == 2 and sys.argv[1] == "--selftest":
        return selftest()
    if selftest():
        return 1
    if len(sys.argv) == 3 and sys.argv[1] == "--base":
        return base_check(sys.argv[2])
    try:
        rows = [l.split("\t") for l in open(TSV, encoding="utf-8").read().splitlines() if l.strip()]
    except FileNotFoundError:
        print(f"::error::{TSV} missing: run `lake env lean scripts/trust/StatementDeps.lean` first")
        return 1
    cert = {}
    for r in rows:
        cert.setdefault(r[0], []).append((r[1], parse_sel_tsv(r[2] if len(r) > 2 else "")))
    params = {}
    try:
        for l in open(PARAMS, encoding="utf-8").read().splitlines():
            if l.strip():
                name, fr = l.split("\t")
                params.setdefault(name, set()).add(Fraction(fr))
    except FileNotFoundError:
        pass
    try:
        ambig_ok = {l.split("#")[0].strip() for l in open(SELBASE, encoding="utf-8") if l.split("#")[0].strip()}
    except FileNotFoundError:
        ambig_ok = set()
    errors = []
    for name in sorted(ambig_ok):
        sels = [c for _, c in cert.get(name, [])]
        if len(set(sels)) == len(sels) and len(sels) > 1:
            errors.append(f"S2: {name} is in {SELBASE} but its certified values have distinct selectors: remove the line")
        elif name not in cert:
            errors.append(f"S2: {SELBASE} lists {name}, which certifies nothing")
    text = open(FINDINGS, encoding="utf-8").read()
    if "## Verified findings" not in text:
        print("::error::FINDINGS.md has no '## Verified findings' section")
        return 1
    # parameters each record fixes, by slot (P1/P2): `fixed` of .lake/meaning.jsonl (explicit numeral arguments of
    # program definitions, by binder) and the `let` arguments of its certified quantities
    fixed = {}
    try:
        import json
        for l in open(".lake/meaning.jsonl", encoding="utf-8"):
            r = json.loads(l)
            if r.get("type") == "headline" and r.get("name", "").startswith("Checked.Records."):
                nm = r["name"].split(".")[-1]
                for f in r.get("fixed", []):
                    if f.get("def") == "RoundsTo":
                        continue  # the certified decimal and its digits are not parameters
                    try:
                        fixed.setdefault(nm, {}).setdefault(f["param"], set()).add(Fraction(norm(f["lit"]).replace(" ", "")))
                    except (ValueError, ZeroDivisionError):
                        pass
    except FileNotFoundError:
        errors.append(".lake/meaning.jsonl missing: run StatementDeps.lean first (P1/P2)")
    # only real-valued parameter slots (ℕ indices such as `cosmoCoeff 5` are not inputs)
    fixed = {nm: {k: vs for k, vs in sl.items() if vs & params.get(nm, set())} for nm, sl in fixed.items()}
    for nm, rows_ in cert.items():
        for _, (_, binds) in rows_:
            for v, x in binds:
                fixed.setdefault(nm, {}).setdefault(v, set()).add(x)
    # the generated section must be current (run 2026-11-08T0028Z)
    table = generated_table(rows)
    g = text.find("\n" + GENERATED)
    cur = None
    if g >= 0:
        k = text.find("\n## ", g + 1)
        cur = text[g + 1:(k + 1 if k >= 0 else len(text))]
    if "--write" in sys.argv:
        new_text = (text[:g + 1] + table + (text[k + 1:] if k >= 0 else "")) if g >= 0 else text.rstrip("\n") + "\n\n" + table
        open(FINDINGS, "w", encoding="utf-8").write(new_text)
        print(f"wrote the generated section of {FINDINGS} ({len(rows)} certified values)")
        text = new_text
    elif cur != table:
        errors.append(f"the section '{GENERATED}' of {FINDINGS} is missing or stale: run "
                      f"`python3 scripts/trust/check_numbers.py --write` after StatementDeps.lean and commit")
    errs, counts = check_text(text, cert, params, ambig_ok, fixed)
    errors += errs
    total = sum(counts.values())
    print(f"certified numbers (FINDINGS.md outside '{UNVERIFIED}'): {counts['✓']} certified [✓], "
          f"{counts['src']} quoted [src], {counts['in']} inputs [in], {counts['unc']} unchecked [unc]; "
          f"{total} tagged")
    for e in errors:
        print(f"::error::{e}")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
