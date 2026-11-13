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
Roles (run 2026-11-08T0628Z; adversary of run 2026-11-08T0028Z, d1 d2 d5 d6: a printed and a true value
swapped in prose, or a difference called q₀, passed every rule above because a record's *role* — printed
formula, derived quantity, difference — was free text). The role of every certified value is computed
from the Lean statement, not from prose: the outermost program definitions of the certified quantity
`x` (those not inside another program definition's arguments) and their labels in
`scripts/trust/def_kinds.txt` (checked labels: PRINTED needs a blind second reading). `printed`: every
outermost definition is PRINTED; `derived`: at least one is not (a pinned or derived quantity of the
program); `free`: none (a formula of numerals or a bound variable such as the `r` of `∃ r`);
`difference(A−B)`: `x` is `u − v` with roles A ≠ B. Rules:
  R0  every certified value whose role is printed, derived or a difference carries it in its tag,
      `0.685[✓F1_printedL0(printed)]`, `0.2153[✓F3_D4_LCDM(correctD4, derived)]`, `0.24[✓F3_D4_LCDM(difference)]`
      (S1/S2 read it), so the role Lean gives a number stands next to it in the text a reader reads.
On the *window* of a certified number (the text of its sentence after the previous tag):
  R1  the last role word of the window agrees with the role: a printed word (printed, misprinted,
      misprint, erroneous, wrong) only before a printed value, a true word (true, correct, corrected,
      actual, exact) only before a derived value;
  R2  a printed value has a printed word in its window (so a swap with a derived value fails R1 or R2);
  R3  a difference: role words in the window, if any, name both sides in the order of the subtraction
      ("true − printed" for derived − printed);
  R4  `q₀ = c[✓…]`, `l₀ ≈ c[✓…]` (the cosmographic symbols q₀ j₀ s₀ l₀ m₀, from the frozen phrases of
      the pinned `decel` and `cosmoCoeff`): a derived value must be that quantity (`decel`,
      `cosmoCoeff n`, n = 3…6); a difference or free value may not be named by a symbol.
The generated table shows each value's role. Open (recorded): free and bound values (roots, sizes) carry
no role; role words outside the closed lists are not read; which derived quantity a value is (beyond
R4's symbols and the selector's head) is still read from the tag's selector, not from prose.

Generated number layout (run 2026-11-08T1428Z; rules G1–G4, see the comment block before `claim_sections`): certified
numbers and bound inputs stand only in generated blocks `<!-- certified: … -->` that quote the record's Lean statement
from CLAIMS.md; author prose carries none (blind red team U, run 0628Z: 6/6 accepted defects were author words beside a
correctly tagged number). `--write` regenerates the blocks, the table and the reading guide.

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
from pathlib import Path
from decimal import Decimal
from fractions import Fraction

FINDINGS = "FINDINGS.md"
TSV = ".lake/records_numbers.tsv"
UNVERIFIED = "## Candidates under verification"

DASHES = "−–—‐‑‒-"
SUP = "⁰¹²³⁴⁵⁶⁷⁸⁹"
NUM = r"[" + DASHES + r"]?\d+(?:\.\d+)?(?:×10[⁻⁺]?[" + SUP + r"]+)?"
SELX = r"(?:\([^()\[\]]*\))?"
TAG = r"\[(✓[A-Za-z0-9_]+" + SELX + r"|in✓[A-Za-z0-9_]+" + SELX + r"|src(?:[=<>][A-Za-z0-9_]+)?|in|unc)\]"  # src=H, src>H, src<H: check_findings.py FB2
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


KINDS_FILE = "scripts/trust/def_kinds.txt"
PRINTED_W = r"printed|misprinted|misprint|erroneous|wrong"
TRUE_W = r"true|correct|corrected|actual|exact"
ROLE_WORD = re.compile(r"(?<![\w])(" + PRINTED_W + "|" + TRUE_W + r")(?![\w])", re.I)
ROLES = ("printed", "derived", "difference", "free")
# cosmographic symbols -> the pinned quantity (frozen phrases of `decel` and `Aviles.cosmoCoeff` in
# scripts/trust/phrases.txt; since run 2026-11-09T0228Z (rule P7 of check_claims.py: phrases are blind texts) the
# letters j, s, l of the orders 3, 4, 5 come from a blind reader (runs/2026-11-09T0228Z/symbols/SYMBOLS.txt). The
# blind reader did not name order 6: m₀ -> order 6 rests on this table alone, not on a phrase (known gap, STATE).
# decel is the deceleration parameter)
SYMBOLS = {"q₀": ("Checked.Cosmography.decel", None), "j₀": ("Checked.Cosmography.Aviles.cosmoCoeff", "3"),
           "s₀": ("Checked.Cosmography.Aviles.cosmoCoeff", "4"), "l₀": ("Checked.Cosmography.Aviles.cosmoCoeff", "5"),
           "m₀": ("Checked.Cosmography.Aviles.cosmoCoeff", "6")}
PHRASE_GUARD = ("order 2 coefficient is minus the deceleration parameter usually written q",
                "order 3 coefficient is the jerk parameter usually written j",
                "order 4 coefficient is the snap parameter usually written s",
                "order 5 coefficient is the lerk parameter usually written l", "the deceleration parameter")


def load_kinds():
    out = {}
    try:
        for l in open(KINDS_FILE, encoding="utf-8"):
            l = l.split("#")[0].split()
            if len(l) == 2:
                out[l[0]] = l[1]
    except FileNotFoundError:
        pass
    return out


def _tokens(x):
    """identifiers, numerals, parentheses and operators of a pretty-printed Lean term"""
    return re.findall(r"[A-Za-z_][\w.'₀-₉⁰-⁹]*|\d+(?:\.\d+)?|:=|[()]|[-+*/^;=∣]|\S", x)


OPS = {"+", "-", "*", "/", "^", ";", ":=", "=", "∣", "have", "let", "fun", "↦", "=>"}


def _parse(toks, i=0):
    """nested lists by parentheses"""
    out = []
    while i < len(toks):
        t = toks[i]
        if t == "(":
            sub, i = _parse(toks, i + 1)
            out.append(sub)
        elif t == ")":
            return out, i + 1
        else:
            out.append(t)
            i += 1
    return out, i


_BODIES = None


def composite_body(full, kinds):
    """parsed body of a COMPOSITE definition, from its generated line in CLAIMS.md (`is defined as `…``), with
    short names resolved to the labelled program constants they name (unique suffix); None if unknown"""
    global _BODIES
    if _BODIES is None:
        _BODIES = {}
        try:
            for l in open("CLAIMS.md", encoding="utf-8"):
                m = re.match(r"- `([^\s`]+)[^`]*` — COMPOSITE\b.*: is defined as `([^`]*)`\s*$", l.rstrip("\n"))
                if m:
                    _BODIES.setdefault(m.group(1), m.group(2))
        except FileNotFoundError:
            pass
    short = full.split(".")[-1]
    body = _BODIES.get(short)
    if body is None:
        return None
    toks = []
    for t in _tokens(body):
        hits = [k for k in kinds if k.endswith("." + t)] if re.match(r"[A-Za-z_]", t) else []
        toks.append(hits[0] if len(hits) == 1 else t)
    items, _ = _parse(toks)
    return items


def _outer(items, kinds, acc):
    """outermost program definitions (head of a juxtaposition run) of a parsed term"""
    run_start = True
    for it in items:
        if isinstance(it, str) and it in OPS:
            run_start = True
            continue
        if run_start:
            if isinstance(it, str) and it.startswith("Checked."):
                # every program constant a headline reaches is labelled or pinned (StatementDeps, T1 blocking)
                body = composite_body(it, kinds) if kinds.get(it) == "COMPOSITE" and len(acc) < 64 else None
                if body is not None:
                    # a COMPOSITE is read through: its role is that of the definitions its body combines (blind
                    # red team W, run 2026-11-08T1428Z, d06: `l0Value Ω := printedAvilesL0 Ω + 0` made a printed
                    # value read as derived in a generated block)
                    _outer(body, kinds, acc)
                else:
                    acc.append((it, kinds.get(it, "PINNED")))
                run_start = False
                skip = True
                continue
            if isinstance(it, list):
                _outer(it, kinds, acc)
            run_start = False
            skip = False
        else:
            # an argument of the run's head: only skipped when the head is a program definition
            if not skip and isinstance(it, list):
                _outer(it, kinds, acc)
    return acc


def _term_role(items, kinds):
    acc = _outer(items, kinds, [])
    if not acc:
        return "free"
    return "printed" if all(k == "PRINTED" for _, k in acc) else "derived"


def role_of(x, kinds):
    """role of a certified quantity (pretty-printed Lean term): printed / derived / free / difference(A−B)"""
    items, _ = _parse(_tokens(x))
    while len(items) == 1 and isinstance(items[0], list):
        items = items[0]
    # top-level binary minus: u − v
    add = [i for i, it in enumerate(items) if it in ("+", "-") and i > 0 and not (isinstance(items[i - 1], str) and items[i - 1] in OPS)]
    if len(add) == 1 and items[add[0]] == "-" and not any(isinstance(t, str) and t in (";", ":=") for t in items):
        i = add[0]
        a, b = _term_role(items[:i], kinds), _term_role(items[i + 1:], kinds)
        # run 2026-11-12T1028Z: a printed or derived quantity minus a bound variable (or the reverse) is a
        # difference too — before, `printedFazioSeparation - β` was labelled "printed value" in the generated block
        if a != b and (a, b) != ("free", "free"):
            return f"difference({a}−{b})"
    # run 2026-11-12T2028Z (blind red team AI, side note): a relative difference `(u − v) / w` (or `c * (u − v)`)
    # was labelled by the roles of all its definitions together ("printed" for (printed − q 0) / printed). A
    # product or quotient with exactly one factor that is a difference of two roles takes that difference's role.
    if not add and all(it in ("*", "/") for it in items if isinstance(it, str) and it in OPS):
        diffs = [r for it in items if isinstance(it, list) for r in [role_of_items(it, kinds)] if r.startswith("difference(")]
        if len(diffs) == 1:
            return diffs[0]
    return _term_role(items, kinds)


def role_of_items(items, kinds):
    while len(items) == 1 and isinstance(items[0], list):
        items = items[0]
    add = [i for i, it in enumerate(items) if it in ("+", "-") and i > 0 and not (isinstance(items[i - 1], str) and items[i - 1] in OPS)]
    if len(add) == 1 and items[add[0]] == "-" and not any(isinstance(t, str) and t in (";", ":=") for t in items):
        a, b = _term_role(items[:add[0]], kinds), _term_role(items[add[0] + 1:], kinds)
        if a != b and (a, b) != ("free", "free"):
            return f"difference({a}−{b})"
    return _term_role(items, kinds)


def head_of(x):
    """(outermost head identifier, first argument) of a pretty-printed term, for R4"""
    t = _tokens(x)
    return (t[0], t[1] if len(t) > 1 else None) if t else (None, None)


def generated_table(rows):
    """FINDINGS.md's generated section: every certified value with the tag that selects it and the quantity
    as Lean states it (run 2026-11-08T0028Z: the binding of a number to its quantity is read from Lean, not
    from prose)."""
    out = [GENERATED, "",
           "Generated by `scripts/trust/check_numbers.py --write` from `.lake/records_numbers.tsv` (written by "
           "`scripts/trust/StatementDeps.lean` from the statements of the record headlines, namespace Records of the "
           "strict library); CI fails if "
           "it is stale. Each row: the tag that selects the value (the selector in parentheses is required when a "
           "record certifies several values), the certified decimal, and the quantity Lean certifies it for "
           "(`RoundsTo x d k`: |x − d| ≤ 10⁻ᵏ/2). Free names (`a`, `t₀`, `r`) are bound in the record's statement; "
           "read the full statement in CLAIMS.md.", "",
           "Role (run 2026-11-08T0628Z): `printed` (every outermost definition of the quantity is labelled "
           "PRINTED: a source's printed formula), `derived` (a pinned or derived quantity of the program), "
           "`difference(A−B)`, or `free` (no program definition: a formula of numerals or a bound variable); "
           "read from the statement and scripts/trust/def_kinds.txt, checked against the prose by rules R0–R4.", "",
           "| tag | value | role | certified quantity |", "|---|---|---|---|"]
    kinds = load_kinds()
    selcount = {}
    for r in rows:
        selcount[(r[0], r[2] if len(r) > 2 else "")] = selcount.get((r[0], r[2] if len(r) > 2 else ""), 0) + 1
    for r in rows:
        name, val = r[0], r[1]
        sel = r[2] if len(r) > 2 else ""
        x = r[3] if len(r) > 3 else ""
        st = sel_tag_text(sel)
        rl = role_of(x, kinds)
        if rl != "free":
            st = ", ".join(([st] if st else []) + ["difference" if rl.startswith("difference(") else rl])
        tag = f"✓{name}" + (f"({st})" if st else "")
        out.append(f"| {tag} | {val.replace('-', '−')} | {role_of(x, kinds)} | `{x.replace('|', '∣')}` |")
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
            # role items (R0) are checked against Lean on every run; adding one is not a change of the pair
            tg = re.sub(r"\(([^()]*)\)$", lambda mm: "(" + ", ".join(x.strip() for x in mm.group(1).split(",")
                        if x.strip() not in ROLES) + ")", t.group(2)).replace("()", "")
            k = (norm(t.group(1)), tg)
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


def check_text(text, cert, params, ambig_ok, fixed=None, roles=None):
    """All FINDINGS rules on `text`. cert: name -> [(value string, selector)]; roles: name -> [(value string,
    selector, role, quantity)] in the same order (rules R1–R4; absent: S-rules only). Returns (errors, counts)."""
    errors, counts = [], {"✓": 0, "src": 0, "in": 0, "unc": 0}
    fixed = fixed or {}
    roles = roles or {}
    for line in scope(text).split("\n"):
        s = code_blank(line)
        tagged_starts = set()
        bound_tags = []   # (start, end, {var: Fraction}) of selector tags with bindings (rule S3)
        tag_spans = []    # (number start, tag end) of every tag (window boundaries of R1–R4)
        role_tags = []    # (number start, tag end, role, quantity, text) of certified values with a known role
        for t in re.finditer(r"(" + NUM + r")" + TAG, s):
            num, tag = t.group(1), t.group(2)
            tagged_starts.add(t.start(1))
            tag_spans.append((t.start(1), t.end()))
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
                role_req = None
                if seltxt is not None:
                    items = [x.strip() for x in seltxt.split(",")]
                    rl = [x for x in items if x in ROLES]
                    if len(rl) > 1:
                        errors.append(f"{num}[{tag}]: the selector names two roles")
                        continue
                    if rl:
                        role_req = rl[0]
                        items = [x for x in items if x not in ROLES]
                        seltxt = ", ".join(items) if items else None
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
                rrows = roles.get(name) or [(v, c, None, "") for v, c in cert[name]]
                # a tag naming only a role selects by role (the conjunct's own selector need not be written)
                byrole = role_req is not None and sel is None
                rmatch = lambda r: role_req is None or r == role_req or (role_req == "difference" and str(r).startswith("difference("))
                same = [(v, c) for v, c, r, _ in rrows if (byrole or c == want) and rmatch(r)]
                rmatch = lambda r: role_req is None or r == role_req or (role_req == "difference" and str(r).startswith("difference("))
                if role_req is not None and not any(value(v) == value(num) and rmatch(r) for v, c, r, _ in rrows):
                    errors.append(f"S1: {num}[{tag}]: {name} certifies {num} with role "
                                  f"{', '.join(str(r) for v, c, r, _ in rrows if value(v) == value(num))}, not {role_req}")
                    continue
                if sel is not None and not any(value(v) == value(num) for v, _ in same):
                    errors.append(f"S1: {num}[{tag}]: {name} certifies {num} with selector "
                                  f"{', '.join(fmt_sel(c) for v, c in cert[name] if value(v) == value(num))}, "
                                  f"not {fmt_sel(want)}")
                    continue
                if len(cert[name]) > 1 and name not in ambig_ok and len(same) != 1:
                    errors.append(f"S2: {num}[{tag}]: {name} certifies several values; the tag must name the selector "
                                  f"of this one: {', '.join(fmt_sel(c) for v, c in cert[name] if value(v) == value(num))}"
                                  + (f" (or its role: {', '.join(str(r) for v, c, r, _ in rrows if value(v) == value(num))})"
                                     if roles.get(name) else ""))
                    continue
                hit = [(r, x) for v, c, r, x in rrows if value(v) == value(num) and (byrole or c == want) and rmatch(r)]
                if not hit and sel is None and role_req is None:
                    hit = [(r, x) for v, c, r, x in rrows if value(v) == value(num)]  # untagged selector: by value
                if len({r for r, _ in hit}) == 1 and hit[0][0] is not None:
                    role_tags.append((t.start(1), t.end(), hit[0][0], hit[0][1], f"{num}[{tag}]"))
                    # R0: the role is written in the tag, next to the number, for every value that has one
                    if role_req is None and hit[0][0] != "free":
                        rr = "difference" if hit[0][0].startswith("difference(") else hit[0][0]
                        errors.append(f"R0: {num}[{tag}]: name the role Lean gives this value in the tag: "
                                      f"{num}[✓{name}({(seltxt + ', ') if seltxt else ''}{rr})]")
                counts["✓"] += 1
            else:
                counts["src" if tag.startswith("src") else tag] += 1
        for t in re.finditer(r"\[(✓[^\]]*|src|in|unc)\]×10", s):
            errors.append(f"power of ten after the tag {t.group()[:-3]}: write it before the tag, 1.3×10⁻⁵[✓name]")
        # an input in a sentence with a certified number must be bound to a record (red team D, D02)
        for sent in re.split(r"(?<=[.;])\s", s):
            if "[✓" in sent and ("[in]" in sent or "[src]" in sent or "[unc]" in sent):
                errors.append(f"bare [in]/[src]/[unc] in a sentence with a certified number: bind the parameter to "
                              f"its record, 0.3[in✓name], or move the quote to its own sentence: {sent.strip()[:90]}")
        # R1–R4: the role of a certified value (read from Lean) agrees with the words next to it (run 2026-11-08T0628Z)
        off = 0
        for sent in re.split(r"(?<=[.;])\s", s):
            a0 = s.find(sent, off)
            off = a0 + len(sent)
            for na, nb, role, x, shown in [rt for rt in role_tags if a0 <= rt[0] < off]:
                prev = max([b for a, b in tag_spans if a0 <= a and b <= na] + [a0])
                window = s[prev:na]
                words = ["P" if re.fullmatch(PRINTED_W, w.lower()) else "T" for w in ROLE_WORD.findall(window)]
                ctx = window.strip()[-70:]
                if role == "printed":
                    if not words:
                        errors.append(f"R2: {shown} is the value of a printed formula (role read from Lean) but no printed "
                                      f"word labels it in its window: …{ctx}…")
                    elif words[-1] != "P":
                        errors.append(f"R1: {shown} is the value of a printed formula but the nearest role word before it "
                                      f"says true/correct: …{ctx}…")
                elif role == "derived":
                    if words and words[-1] == "P":
                        errors.append(f"R1: {shown} is a derived quantity (role read from Lean: not every outermost "
                                      f"definition is PRINTED) but the nearest role word before it says printed: …{ctx}…")
                elif role.startswith("difference("):
                    a, b = role[len("difference("):-1].split("−")
                    want = ["P" if a == "printed" else "T", "P" if b == "printed" else "T"]  # derived: a true word
                    if words and not (words[0] == want[0] and want[1] in words[1:]):
                        errors.append(f"R3: {shown} is the difference {a} − {b} (read from Lean) but the role words of its "
                                      f"window are in another order: …{ctx}…")
                sm = re.search(r"(?<![\w])(" + "|".join(SYMBOLS) + r")\s*[=≈]\s*\+?$", s[a0:na])
                if sm:
                    sym = sm.group(1)
                    if role == "derived":
                        h, arg = head_of(x)
                        if (h, arg if SYMBOLS[sym][1] else None) != SYMBOLS[sym]:
                            errors.append(f"R4: prose `{sym} = {shown}` but the certified quantity is `{x[:60]}`, not {sym}")
                    elif role != "printed":
                        errors.append(f"R4: prose `{sym} = {shown}` but the certified value is {role} (read from Lean), "
                                      f"not the quantity {sym}")
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
    # roles (R1–R4, run 2026-11-08T0628Z): P = printed formula, V = program quantity, D = difference, Z = q₀
    cert["P"] = [("0.685", ("", frozenset()))]
    cert["V"] = [("3.115", ("cosmoCoeff", frozenset()))]
    cert["D"] = [("0.24", ("", frozenset()))]
    cert["Z"] = [("-0.55", ("decel", frozenset()))]
    cert["W"] = [("0.277", ("", frozenset())), ("-5.25", ("", frozenset()))]
    roles = {"P": [("0.685", cert["P"][0][1], "printed", "Checked.X.printedL0 (3 / 10)")],
             "V": [("3.115", cert["V"][0][1], "derived", "Checked.Cosmography.Aviles.cosmoCoeff 5 a t₀")],
             "D": [("0.24", cert["D"][0][1], "difference(printed−derived)", "Checked.X.p a - Checked.X.c a")],
             "Z": [("-0.55", cert["Z"][0][1], "derived", "Checked.Cosmography.decel a t₀")],
             "W": [("0.277", ("", frozenset()), "printed", "x"), ("-5.25", ("", frozenset()), "derived", "y")]}
    cases += [
        ("the printed l₀ is 0.685[✓P(printed)] instead of 3.115[✓V(derived)].", None),
        ("the printed l₀ is 0.685[✓P] instead of 3.115[✓V(derived)].", "R0"),
        ("the printed l₀ is 3.115[✓V(derived)] instead of 0.685[✓P(printed)].", "R1"),
        ("the formula's l₀ is 3.115[✓V(derived)] instead of 0.685[✓P(printed)].", "R2"),
        ("the printed l₀ is 0.685[✓P(derived)] instead of 3.115[✓V(derived)].", "S1"),
        ("printed − true = 0.24[✓D(difference)], at q₀ = −0.55[✓Z(decel, derived)].", None),
        ("true − printed = 0.24[✓D(difference)].", "R3"),
        ("off by −0.55[✓Z(decel, derived)] at q₀ = +0.24[✓D(difference)].", "R4"),
        ("printed 0.277[✓W(printed)] instead of −5.25[✓W(derived)].", None),
        ("printed −5.25[✓W(derived)] instead of 0.277[✓W(printed)].", "R1"),
        ("printed 0.277[✓W] instead of −5.25[✓W(derived)].", "S2"),
    ]
    bad = []
    kinds = load_kinds()
    if kinds and role_of("Checked.Cosmography.CCS.printedD4 (Checked.Cosmography.decel a t₀) b c d - "
                         "Checked.Cosmography.CCS.correctD4 (Checked.Cosmography.decel a t₀) b c d", kinds) \
            != "difference(printed−derived)":
        bad.append("role_of does not read printedD4 − correctD4 as difference(printed−derived)")
    if kinds and role_of("(Checked.Records.printedFazioWall - q 0) / Checked.Records.printedFazioWall", kinds) \
            != "difference(printed−free)":
        bad.append("role_of does not read a relative difference (printed − q 0) / printed as difference(printed−free) (AI side note)")
    if kinds:
        global _BODIES
        composite_body("Checked.X", kinds)  # load CLAIMS.md bodies first
        _BODIES["wrapZZ"] = "printedAvilesL0 Ω + 0"
        k2 = dict(kinds, **{"Checked.Records.wrapZZ": "COMPOSITE"})
        if role_of("Checked.Records.wrapZZ (3 / 10)", k2) != "printed":
            bad.append("role_of does not read through a COMPOSITE wrapper of a PRINTED definition (W d06)")
        del _BODIES["wrapZZ"]
    for text, rule in cases:
        errs, _ = check_text(head + text + "\n", cert, params, set(), fixed, roles)
        fired = {e.split(":")[0] for e in errs}
        if rule is None and errs:
            bad.append(f"clean control rejected: {text} -> {errs}")
        if rule is not None and rule not in fired:
            bad.append(f"control for {rule} not rejected: {text} -> {errs}")
    ng, gbad = g_selftest(kinds)
    bad += gbad
    for b in bad:
        print(f"::error::check_numbers selftest: {b}")
    print(f"check_numbers selftest: {len(cases) + ng} controls, {len(bad)} failing")
    return 1 if bad else 0


# ---------------------------------------------------------------------------------------------------------------
# Generated number sentences (run 2026-11-08T1428Z; blind red team U, run 2026-11-08T0628Z: 6/6 valid defects put
# the falsehood in author prose *beside* a correctly tagged certified number — a range phrase, a coefficient, a
# direction word, a unit, an input's symbol, the attribution of a free value). Rules on the words around a tag
# have been routed around in every round since F (PROMPT working note "Filtering prose does not converge; generate
# it"). So a certified number no longer stands in an author's sentence at all:
#   G1  in the scope of FINDINGS.md, a certified tag [✓…] or a bound input [in✓…] stands only inside a generated
#       block, and outside the blocks no number may equal (in absolute value) a certified value of any record;
#   G2  each block `<!-- certified: R1 R2 … -->` … `<!-- /certified -->` is exactly what `--write` generates for the
#       records it names: per record its Lean statement quoted from CLAIMS.md (binders, assumptions, conclusion,
#       program definitions other than RoundsTo), then one line per certified value (the quantity as Lean states
#       it, the value with its tag, its role) and the order of every printed/derived pair of the record, decided
#       from the two certified roundings;
#   G3  every record of .lake/records_numbers.tsv is named by exactly one block.
# Author prose may refer to a record by name ("certified below"); it can no longer attach a scope, a direction, a
# unit, a coefficient or a symbol to a certified number, because the number is not in its sentence. What remains
# author prose is labelled as such by the banner at the top of FINDINGS.md (G4).
BLOCK_OPEN = re.compile(r"^<!-- certified: ([A-Za-z0-9_ ]+?) -->$")
BLOCK_CLOSE = "<!-- /certified -->"
BANNER = ("**Reading guide (generated layout, rule G4 of `scripts/trust/check_numbers.py`):** a number is "
          "machine-checked only inside a block headed *Certified numbers (generated)*: there it stands next to "
          "the Lean statement that certifies it, quoted from CLAIMS.md. Every other sentence of this file is "
          "author prose: it may explain, but it carries no certified number and is not checked by Lean.")
CLAIMS = "CLAIMS.md"


def claim_sections(claims_text):
    """CLAIMS.md: headline short name -> (statement lines, definition lines other than RoundsTo)"""
    out = {}
    for sec in re.split(r"\n(?=## `)", claims_text):
        m = re.match(r"## `([^`]+)`\n", sec)
        if not m:
            continue
        body = sec[m.end():]
        stmt, defs = [], []
        part = "pre"
        for l in body.split("\n"):
            if l.startswith("Full name "):
                part = "stmt"
                continue
            if l.startswith("Program definitions in this claim"):
                part = "defs"
                continue
            if l.startswith("Author's paraphrase"):
                break
            if part == "stmt" and l.strip():
                stmt.append(l)
            elif part == "defs" and l.startswith("- ") and not l.startswith("- `RoundsTo "):
                # evidence pointers (pin theorems, agreement theorems) are not headlines: STATE.md/FINDINGS.md may
                # cite only registered headlines (StatementDeps records rule); CLAIMS.md keeps them
                l = re.sub(r" \((?:pin theorem )?`[^`]*(?:_pins|Checked\.Trust\.[^`]*)`\)", "", l)
                defs.append(l)
        out[m.group(1)] = (stmt, defs)
    return out


def _enclosure(v, k):
    d = Fraction(Decimal(norm(v)))
    h = Fraction(1, 2 * 10 ** k)
    return d - h, d + h


def _digits(v):
    v = norm(v)
    return len(v.split(".")[1]) if "." in v else 0


def short(x):
    """Lean's quantity with namespaces dropped, as CLAIMS.md prints it"""
    return re.sub(r"\bChecked(?:\.[A-Za-z_][\w']*)*\.(?=[A-Za-z_][\w']*)", "", x).replace("|", "∣")


def block_text(names, rows, claims, kinds):
    """the generated content of one block (G2)"""
    sel_rows = {}
    for r in rows:
        sel_rows.setdefault(r[0], []).append(r)
    out = ["- **Certified numbers (generated by `scripts/trust/check_numbers.py --write` from the Lean records and "
           "CLAIMS.md; do not edit).** Each value below is a conjunct `RoundsTo x d k` (|x − d| ≤ 10⁻ᵏ/2) of the "
           "quoted Lean statement:"]
    for nm in names:
        stmt, defs = claims.get(nm, ([], []))
        out.append(f"  - `Checked.Records.{nm}`, as Lean states it:")
        for n, l in enumerate(stmt + (["where"] + defs if defs else [])):
            if n:
                out.append("    >")
            # one-word code spans (binder names such as `n`, `a`, `Ω`) in italics: STATE.md/FINDINGS.md code spans
            # without a space are read as theorem citations by the StatementDeps records rule
            out.append("    > " + re.sub(r"`([^`\s]+)`", r"*\1*", l))
        vals = []
        for r in sel_rows.get(nm, []):
            val, sel, x = r[1], (r[2] if len(r) > 2 else ""), (r[3] if len(r) > 3 else "")
            rl = role_of(x, kinds) if x else "free"
            st = sel_tag_text(sel)
            if rl != "free":
                st = ", ".join(([st] if st else []) + ["difference" if rl.startswith("difference(") else rl])
            tag = f"✓{nm}" + (f"({st})" if st else "")
            word = {"printed": "printed value", "derived": "derived value", "free": "value"}.get(
                rl, "difference" if rl.startswith("difference(") else rl)
            k = _digits(val)
            out.append(f"    - {word}: `{short(x)}` rounds to {val.replace('-', '−')}[{tag}] at {k} "
                       f"decimal{'s' if k != 1 else ''}; role {rl.replace('-', '−')}.")
            vals.append((rl, x, val, k))
        one_each = [v[0] for v in vals].count("printed") == 1 and [v[0] for v in vals].count("derived") == 1
        for rp, xp, vp, kp in vals:
            if rp != "printed":
                continue
            for rd, xd, vd, kd in vals:
                # a printed formula and the program's quantity of the same arguments (or the record's only pair)
                if rd != "derived" or not (one_each or _tokens(xp)[1:] == _tokens(xd)[1:]):
                    continue
                lp, hp = _enclosure(vp, kp)
                ld, hd = _enclosure(vd, kd)
                if hp < ld:
                    rel = "below"
                elif lp > hd:
                    rel = "above"
                else:
                    rel = "not separated by the two roundings from"
                out.append(f"    - order, from the two roundings: the printed value `{short(xp)}` is "
                           f"{rel} the derived value `{short(xd)}`.")
    return out


def render_blocks(text, rows, claims, kinds):
    """replace the content of every block by its generated text"""
    lines, out, i = text.split("\n"), [], 0
    while i < len(lines):
        out.append(lines[i])
        m = BLOCK_OPEN.match(lines[i])
        if m:
            j = i + 1
            while j < len(lines) and lines[j] != BLOCK_CLOSE:
                j += 1
            out += block_text(m.group(1).split(), rows, claims, kinds)
            if j < len(lines):
                out.append(BLOCK_CLOSE)
            i = j + 1
            continue
        i += 1
    return "\n".join(out)


def strip_blocks(text):
    """(text with every block's lines blanked, text of the blocks only): rules G1 and the prose rules read the
    first; the tag rules read the second without its quoted Lean lines (G2 makes those exact)"""
    prose, gen, inside = [], [], False
    for l in text.split("\n"):
        if BLOCK_OPEN.match(l):
            inside = True
            prose.append("")
            gen.append("")
            continue
        if l == BLOCK_CLOSE:
            inside = False
            prose.append("")
            gen.append("")
            continue
        if inside:
            prose.append("")
            gen.append("" if l.lstrip().startswith(">") else l)
        else:
            prose.append(l)
            gen.append(l if l.startswith("#") else "")
    return "\n".join(prose), "\n".join(gen)


def check_g(text, rows, claims, kinds):
    """G1–G4 on FINDINGS.md text (rows: records_numbers.tsv)"""
    errors = []
    if BANNER not in text:
        errors.append("G4: the reading guide (BANNER of check_numbers.py) is missing at the top of FINDINGS.md: "
                      "run --write")
    regenerated = render_blocks(text, rows, claims, kinds)
    if regenerated != text:
        errors.append("G2: a certified-numbers block differs from what `check_numbers.py --write` generates "
                      "(edited, stale, or unclosed)")
    named = []
    for l in text.split("\n"):
        m = BLOCK_OPEN.match(l)
        if m:
            named += m.group(1).split()
    recs = sorted({r[0] for r in rows})
    for nm in recs:
        if named.count(nm) != 1:
            errors.append(f"G3: record {nm} is named by {named.count(nm)} certified-numbers blocks (exactly one)")
    for nm in sorted(set(named) - set(recs)):
        errors.append(f"G3: a block names {nm}, which certifies no number")
    certvals = {abs(value(r[1])[0]) for r in rows}
    prose, _ = strip_blocks(scope(text))
    for line in prose.split("\n"):
        s = code_blank(line)
        for t in re.finditer(r"\[(?:in)?✓[^\]]*\]", s):
            errors.append(f"G1: certified tag {t.group()} outside a generated block (certified numbers and their "
                          f"inputs stand only in the blocks): …{s[max(0, t.start() - 50):t.end()].strip()}…")
        for t in re.finditer(r"(?<![\w.])(" + NUM + r")(?!\d)(?!\.\d)", s):
            num = t.group(1)
            if not ("." in num or "×10" in num):
                # an integer is read only when signed or after ≈/≃/= (a journal volume "PRD 86" is not a value)
                if not (norm(num).startswith("-") or s[:t.start()].rstrip().endswith(("≈", "≃", "=", "~"))):
                    continue
            v = abs(value(num)[0])
            if v in certvals and not re.fullmatch(r"\d{4}\.\d{4,5}", num):
                errors.append(f"G1: {t.group(1)} equals a certified value but stands in author prose (refer to the "
                              f"record by name; the value is in its generated block): "
                              f"…{s[max(0, t.start() - 50):t.end() + 10].strip()}…")
    errors += check_refs(prose, rows, kinds)
    return errors


FRAC = r"[" + DASHES + r"]?\d+\s*/\s*\d+"


def check_refs(prose, rows, kinds):
    """G5/G6 (run 2026-11-08T1428Z, after blind round V — not blind): author prose that *names* a record.
      G5  a fraction p/q in prose may not equal a certified value (G1 for fractions); in a sentence that names a
          record (`F11_sizes`), `v = c` (c a decimal or a fraction) with v a parameter the record fixes must be one
          of the values Lean fixes it to (round V d03: "its size at q₀ = −1/2 … `F11_sizes`", certified at −0.8);
      G6  the nearest role word (printed/true lists of R1, and `derived`) before a record's name, in its sentence
          and after the previous record name, agrees with the role of the record's values when they all share one
          (round V d01: "the printed formula's value (`F1_l0`)")."""
    errors = []
    signed = {value(r[1])[0] for r in rows}  # a coefficient 7/8 is not the certified −0.875: fractions compare signed
    roles, binds = {}, {}
    for r in rows:
        roles.setdefault(r[0], set()).add(role_of(r[3], kinds) if len(r) > 3 and r[3] else "free")
        for v, x in parse_sel_tsv(r[2] if len(r) > 2 else "")[1]:
            binds.setdefault(r[0], {}).setdefault(v, set()).add(x)
    names = sorted(roles, key=len, reverse=True)
    role_re = re.compile(r"(?<![\w])(" + PRINTED_W + "|" + TRUE_W + r"|derived)(?![\w])", re.I)
    for line in prose.split("\n"):
        for m in re.finditer(r"(?<![\w.])(" + FRAC + r")(?![\d/])", line):
            a, b = norm(m.group(1)).replace(" ", "").split("/")
            if int(b) and Decimal(int(a)) / Decimal(int(b)) in signed:
                errors.append(f"G5: the fraction {m.group(1)} equals a certified value but stands in author prose: "
                              f"…{line[max(0, m.start() - 50):m.end() + 10].strip()}…")
        for sent in re.split(r"(?<=[.;])\s+", line):
            refs = [(m.start(), m.group(1)) for m in re.finditer(r"`(" + "|".join(map(re.escape, names)) + r")`", sent)] if names else []
            for _, nm in refs:
                for m in re.finditer(r"(?<![\w])([^\W\d][\w'₀-₉ₐ-ₜ]*)\s*=\s*(" + FRAC + "|" + NUM + r")(?![\d/.])", sent):
                    v, c = m.group(1), m.group(2)
                    if v not in binds.get(nm, {}):
                        continue
                    if "/" in c:
                        a, b = norm(c).replace(" ", "").split("/")
                        x = Fraction(int(a), int(b)) if int(b) else None
                    else:
                        x = Fraction(value(c)[0])
                    if x not in binds[nm][v]:
                        errors.append(f"G5: `{nm}` fixes {v} to {sorted(str(y) for y in binds[nm][v])}, but its sentence says "
                                      f"{v} = {c}: …{sent[max(0, m.start() - 40):m.end() + 40].strip()}…")
            prev = 0
            for pos, nm in refs:
                rl = {("difference" if r.startswith("difference(") else r) for r in roles[nm]}
                words = role_re.findall(sent[prev:pos])
                prev = pos + len(nm) + 2
                if not words or len(rl) != 1 or rl & {"free", "difference"}:
                    continue  # a free value (root, size) or a difference has no single printed/derived role
                w = words[-1].lower()
                kind = "printed" if re.fullmatch(PRINTED_W, w, re.I) else "derived"
                (r,) = rl
                if r != kind:
                    errors.append(f"G6: `{nm}` certifies {r} values, but the nearest role word before its name is "
                                  f"'{words[-1]}': …{sent[max(0, pos - 60):pos + len(nm) + 2].strip()}…")
    return errors


def generated_printed_ok(text):
    """{line} of verified findings' Printed lines that equal, character for character, what
    check_findings.generated_printed writes from CLAIMS.md and the blind readings (FB10/FB11, run 2026-11-13T1828Z):
    such a line quotes Lean definition bodies and a blind reader's words, not the author's, so its code spans are not
    prose numbers. A line that differs from the generator is read like prose (and FB10 rejects it)."""
    try:
        sys.path.insert(0, str(Path(__file__).resolve().parent))
        import check_findings as CF  # noqa: E402
        cb = CF.claims_blocks(open(CLAIMS, encoding="utf-8").read())
    except (ImportError, OSError):
        return set()
    ok = set()
    for k, body in CF.sections_full(text).items():
        g = CF.generated_printed(k, body, cb)
        if g in body.split("\n"):
            ok.add(g)
    return ok


def blank_quotes(text):
    """the quoted Lean lines of the generated blocks are exact by G2; the number rules read the rest"""
    out, inside = [], False
    gen = generated_printed_ok(text) if "- **Printed (generated" in text else set()
    for l in text.split("\n"):
        if l in gen:
            out.append(re.sub(r"`[^`]*`", lambda mm: " " * len(mm.group()), l))
            continue
        if BLOCK_OPEN.match(l):
            inside = True
        elif l == BLOCK_CLOSE:
            inside = False
        if inside and (l.lstrip().startswith(">") or BLOCK_OPEN.match(l)):
            l = ""
        elif inside:
            # a generated value line: its code spans are Lean's quantity, exact by G2 (not prose numbers)
            l = re.sub(r"`[^`]*`", lambda mm: " " * len(mm.group()), l)
        out.append(l)
    return "\n".join(out)


def g_selftest(kinds):
    """controls for G1–G3: a rejecting case and a clean twin each"""
    rows = [["R", "0.56", "z=1/1", "100 * have z := 1; z"], ["P", "0.685", "@printedAvilesL0;Ω=3/10", "Checked.Records.printedAvilesL0 (3 / 10)"]]
    claims = {"R": (["**It holds that**", "- `RoundsTo (100 * have z := 1; z) 0.56 2`"], []),
              "P": (["**It holds that**", "- `RoundsTo (printedAvilesL0 (3 / 10)) 0.685 3`"], [])}
    head = "# F\n\n" + BANNER + "\n\n## Verified findings\n\n"
    blk = "<!-- certified: R P -->\n" + "\n".join(block_text(["R", "P"], rows, claims, kinds)) + "\n" + BLOCK_CLOSE + "\n"
    cases = [
        (head + "The size is small.\n" + blk, None),
        (head + "The size is 0.56[✓R(z=1)] % up to z = 5.\n" + blk, "G1"),
        (head + "The size is 0.56 % up to z = 5.\n" + blk, "G1"),
        (head + "The printed value is too high.\n" + blk.replace("rounds to 0.685", "rounds to 0.686"), "G2"),
        (head + "The size is small.\n" + blk.replace("certified: R P", "certified: R"), "G3"),
        (("# F\n\n## Verified findings\n\nThe size is small.\n" + blk), "G4"),
        (head + "The size at z = 1 is certified below (`R`).\n" + blk, None),
        (head + "The size at z = 3 is certified below (`R`).\n" + blk, "G5"),
        (head + "The size is 56/100 of a percent.\n" + blk, "G5"),
        (head + "The coefficient is −56/100 here.\n" + blk, None),
        (head + "The printed value (`P`) and the size (`R`) are below.\n" + blk, None),
        (head + "The true value (`P`) is below.\n" + blk, "G6"),
    ]
    bad = []
    for t, rule in cases:
        fired = {e.split(":")[0] for e in check_g(t, rows, claims, kinds)}
        if rule is None and fired:
            bad.append(f"clean G control rejected: {fired}")
        if rule is not None and rule not in fired:
            bad.append(f"control for {rule} not rejected (fired: {fired})")
    return len(cases), bad


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
    cert, roles = {}, {}
    kinds = load_kinds()
    for r in rows:
        cert.setdefault(r[0], []).append((r[1], parse_sel_tsv(r[2] if len(r) > 2 else "")))
        x = r[3] if len(r) > 3 else ""
        roles.setdefault(r[0], []).append((r[1], parse_sel_tsv(r[2] if len(r) > 2 else ""), role_of(x, kinds) if x else None, x))
    try:
        ph = open("scripts/trust/phrases.txt", encoding="utf-8").read()
        for g in PHRASE_GUARD:
            if g not in ph:
                print(f"::error::R4: the frozen phrase of decel/cosmoCoeff no longer contains {g!r}: update SYMBOLS")
                return 1
    except FileNotFoundError:
        pass
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
    try:
        claims = claim_sections(open(CLAIMS, encoding="utf-8").read())
    except FileNotFoundError:
        claims = {}
        errors.append(f"{CLAIMS} missing (rule G2 quotes the Lean statements from it)")
    if "--write" in sys.argv:
        new_text = (text[:g + 1] + table + (text[k + 1:] if k >= 0 else "")) if g >= 0 else text.rstrip("\n") + "\n\n" + table
        new_text = render_blocks(new_text, rows, claims, kinds)
        if BANNER not in new_text:
            a = new_text.find("\n\n", new_text.find("\n\n") + 2)
            new_text = new_text[:a] + "\n\n" + BANNER + new_text[a:]
        open(FINDINGS, "w", encoding="utf-8").write(new_text)
        print(f"wrote the generated section and blocks of {FINDINGS} ({len(rows)} certified values)")
        text = new_text
    elif cur != table:
        errors.append(f"the section '{GENERATED}' of {FINDINGS} is missing or stale: run "
                      f"`python3 scripts/trust/check_numbers.py --write` after StatementDeps.lean and commit")
    errors += check_g(text, rows, claims, kinds)
    errs, counts = check_text(blank_quotes(text), cert, params, ambig_ok, fixed, roles)
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
