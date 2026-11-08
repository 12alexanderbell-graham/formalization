#!/usr/bin/env python3
"""Numeric literals of headline statements are source data that must be read twice (run 2026-11-06T0228Z,
part 3; written blind to red team M). Blocking in CI.

Why: a headline may enter source data as literals of its own statement instead of through a PRINTED
definition — the κ(ω) correlation coefficients `0.480 + 1.574·ω − 0.176·ω²` of
`Checked/Chemistry/SRKAcentric.lean` (likewise `PRAcentric.lean`, `PR78Acentric.lean`), the reduced
temperature `7 / 10`, a "printed" formula written inline in a refutation. The label rules of
StatementDeps.lean read definitions, not statement literals, so nothing read such literals a second time:
a new sibling headline with a wrong coefficient was accepted by every check. This script closes the class.

  python3 scripts/trust/check_literals.py              rules 1-4 on the current tree (reads .lake/meaning.jsonl)
  python3 scripts/trust/check_literals.py --base SHA   also: baseline shrink-only, readings registry changes disclosed
  python3 scripts/trust/check_literals.py --report     print each headline's uncovered literals, never fail

Every numeric literal (numeral, decimal, `(n : ℝ)`) written in the statement of a headline
(`scripts/trust/headlines.txt`, located through `.lake/meaning.jsonl`) is classified, and must be:
 (a) a certified target of the conclusion: in a positive position (not under `¬`, not left of an `→`, not
     in a quantifier's binder, not on either side of `≠`, `↔`), (a1) the last two arguments (value, digits)
     of `RoundsTo` (a negative value written `(-d)` included, run 2026-11-08T0628Z), or (a2) a literal of a side of `=`, `≤`, `<`, `≥`, `>`, `∈` that consists only of
     numerals, `+ - * / ^`, parentheses, type ascriptions and `Set.Icc/Ico/Ioc/Ioo` — the side the
     proof certifies (not for `=` whose other side is a bare variable: `∃ k, k = 0.480 + … ∧ …` defines k); or
 (a3) the numeral `0` or `1` standing alone as one side of a comparison (`0 < b`, `x ≠ 0`, `1 ≤ n`): domain
     hypotheses, not data; or
 (a5) (run 2026-11-06T1428Z) the one number `c` (numeral or quotient of two numerals) of a top-level
     hypothesis `(h : c ≤ S)`, S a top-level `ℝ` binder whose every other occurrence is the right end of an
     interval used only as a domain (`∀ x ∈ Icc a S, …`, `HasDerivWithinAt f f' (Icc a S) x`; not compared,
     measured or spelled otherwise) and that no other binder bounds: a domain length the proof certifies, not
     data (every instance of the theorem is free of c; see `domain_ends`). Recorded limit (adversary, run
     1428Z): a source end time T written as such a c with a wrong value moves the ray of covered instances
     (the claim then does not cover T); CLAIMS.md shows the ray, and an end time that is also an evaluation
     point (`y T`) is never exempt; or
 (a4) a numeral argument of a PINNED definition whose value is recorded in `fixed` of meaning.jsonl for that
     definition (`cosmoCoeff 4`: the meaning of the slot is the pinned definition's frozen phrase); or
 (b) covered by a literal reading registered for the headline in `scripts/trust/literal_readings.txt`
     (`<headline, unique suffix> <reader constant> [<reader constant> ...]`, optional
     `source=<Name>[,<Name>]` field read by check_source_names.py). A reader constant is a `def` of a
     non-generated `Checked/Trust/SecondReading*.lean` module (so check_provenance.py rules 3-4 and
     check_blind_route.py apply: a blind reader's file under `runs/` next to its brief, committed first).
     Its body, with its explicit binders as wildcards (each matches one token or one bracketed group of
     the statement) and numerals compared by exact value (`0.48` = `0.480`), must occur as a contiguous
     token span of the statement; every literal matched by a numeral of the body is covered (since run
     2026-11-07T0828Z not a literal inside a group a binder wildcard matched: nobody read that one). Operators, signs,
     exponents and parenthesisation are thereby compared too, not just values. Each registered constant
     must match at least once (a stale registration fails). Value mode (run 2026-11-06T0628Z): a reader
     constant without binders whose body is a closed arithmetic expression (numerals, `+ - * / ^`,
     parentheses; no division by zero), or a tuple `(e1, ..., en)` of such, also covers statement
     *atoms* of exactly the same value — an atom is a numeral or a parenthesised closed arithmetic group that
     is not an operand of a neighbouring operator — a tuple a run of n consecutive atoms with the values in
     order (`robInit := (1, 0, 0)` covers the arguments `1 0 0`; `robK1 := 4 / 100` covers `(1 / 25)`). A registered `source=` name must occur in a
     brief (`*brief*.md`) of the run folder of the reader module's `runs/` copy; or
 (c) listed for that headline in the shrink-only `scripts/trust/literal_baseline.txt`
     (`<headline> | <uncovered literals in statement order> | <reason>`), populated from the tree at
     run 2026-11-06T0228Z. The list must equal the headline's uncovered literals exactly: a changed,
     added or removed literal fires again; a new headline (a sibling) has no entry.
Rule 2 (hidden literals): every number in `nums` of the headline's meaning.jsonl record (the literals of the
  elaborated statement) other than 0 and 1 must be the value of a literal written in the statement source,
  its negation, or a quotient of two such values (meaning.jsonl records `a / b` and `-a` as numbers), or a
  literal of a program declaration the statement names (transitively, depth 3). Grandfathered in the same
  baseline as `<headline> | hidden: <values> | <reason>` (two `local notation` uses in Records/Findings.lean).
  (`notation`, `macro`, local instances or `OfNat` tricks that bring a number into the statement without
  writing it fail).
Rule 3 (registry hygiene): every registry/baseline headline resolves to exactly one headline; registered
  constants exist and are readers' constants.
Rule 4 (--base): the baseline may only shrink (no added entry; a line's literal list may only lose literals,
  keeping the order of the rest — run 2026-11-06T0228Z, so a partial reading can land); a line added to or
  changed in `literal_readings.txt` needs a LEDGER.md addition naming the headline's last name component.

Not satisfiable by prose: coverage is a token match against a reader's Lean constant, and the baseline
admits only what the tree held when the rule was written. Limits: whether the reader was blind is
check_blind_route.py's (partly uncheckable) business; literals hidden in definitions are the label rules'
business (COMPOSITE: no arithmetic numerals; FORMULA/MATH/WITNESS/PRINTED: second version); a statement
whose source data enter without any numeral (named Mathlib constants such as `Real.pi`, `Real.exp 1`) is
not a literal and is not read here.
"""
import json
import re
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_provenance as P  # noqa: E402  (comment stripping, declarations, runs/ copies)

ROOT = Path(__file__).resolve().parents[2]
MEANING = ROOT / ".lake/meaning.jsonl"
READINGS = "scripts/trust/literal_readings.txt"
BASELINE = "scripts/trust/literal_baseline.txt"
OPEN, CLOSE = "([{⦃⟨", ")]}⦄⟩"
NUMTOK = re.compile(r"\d+(?:\.\d+)?(?:[eE][-+]?\d+)?")
TOK = re.compile(r"«[^»]*»|[^\W\d][\w'!?₀-₉ₐ-ₜ]*(?:\.(?:«[^»]*»|[^\W\d][\w'!?₀-₉]*))*|\d+(?:\.\d+)?(?:[eE][-+]?\d+)?"
                 r"|:=|→|↔|≠|≤|≥|∃!|\S")
RELS = {"=", "≤", "<", "≥", ">", "∈"}
SETS = {"Set.Icc", "Set.Ico", "Set.Ioc", "Set.Ioo", "Icc", "Ico", "Ioc", "Ioo"}
ARITH = set("+-*/^()") | {"−", "·"}
TYPES = {"ℝ", "ℕ", "ℤ", "ℚ"}


def is_subseq(a, b):
    it = iter(b)
    return all(x in it for x in a)


def is_num(t):
    return bool(NUMTOK.fullmatch(t))


def value(t):
    m = re.fullmatch(r"(\d+(?:\.\d+)?)(?:[eE]([-+]?\d+))?", t)
    v = Fraction(m.group(1))
    return v * Fraction(10) ** int(m.group(2)) if m.group(2) else v


# ------------------------------------------------------------------ statements
def statement_text(module, full):
    """Source text of the statement of theorem `full` (binders and type, comments stripped)."""
    rel = module.replace(".", "/") + ".lean"
    p = ROOT / rel
    if not p.exists():
        return None
    text = p.read_text()
    clean = P.strip_comments(text)
    decls, _ = P.declarations(text)
    for nm, pos, _ in decls:
        if nm == full:
            seg = clean[pos:]
            m = re.match(r"[^\n]*?\b(?:theorem|lemma)\s+\S+", seg)
            if not m:
                return None
            i, d = m.end(), 0
            while i < len(seg):
                c = seg[i]
                if c in OPEN:
                    d += 1
                elif c in CLOSE:
                    d -= 1
                elif d == 0 and seg.startswith(":=", i):
                    break
                i += 1
            return seg[m.end():i]
    return None


def lex(s):
    """Tokens with `(n : ℝ)` folded into the numeral n (an ascription is not data)."""
    raw = TOK.findall(s)
    out, i = [], 0
    while i < len(raw):
        if raw[i] == "(" and i + 4 < len(raw) and is_num(raw[i + 1]) and raw[i + 2] == ":" \
                and raw[i + 3] in TYPES and raw[i + 4] == ")":
            out.append(raw[i + 1])
            i += 5
            continue
        out.append(raw[i])
        i += 1
    return out


def group_end(toks, i):
    """index after the bracketed group starting at toks[i] (or i+1 for a single token)"""
    if toks[i] not in OPEN:
        return i + 1
    d = 0
    for j in range(i, len(toks)):
        if toks[j] in OPEN:
            d += 1
        elif toks[j] in CLOSE:
            d -= 1
            if d == 0:
                return j + 1
    return len(toks)


def split_top(toks, lo, hi, seps):
    """split toks[lo:hi] at top-level separators; returns [(a, b)] index ranges"""
    parts, d, start = [], 0, lo
    for j in range(lo, hi):
        t = toks[j]
        if t in OPEN:
            d += 1
        elif t in CLOSE:
            d -= 1
        elif d == 0 and t in seps:
            parts.append((start, j))
            start = j + 1
    parts.append((start, hi))
    return parts


def classify(toks):
    """{index of numeral token: reason it is exempt} for (a1)-(a3) (a4 is applied by the caller)"""
    ok = {}
    # binders before the top-level `:` are hypotheses
    i, n = 0, len(toks)
    while i < n and toks[i] in OPEN:
        i = group_end(toks, i)
    if i < n and toks[i] == ":":
        i += 1
    zero_one_sides(toks, 0, n, ok)
    positive(toks, i, n, ok)
    domain_ends(toks, i, ok)
    return ok


def _one_num(seg):
    """a numeral, or a quotient `a / b` of two numerals (b not zero)"""
    if len(seg) == 1:
        return is_num(seg[0])
    return len(seg) == 3 and is_num(seg[0]) and seg[1] == "/" and is_num(seg[2]) and value(seg[2]) != 0


WITHIN = {"HasDerivWithinAt", "ContinuousWithinAt", "ContinuousOn", "DifferentiableOn", "HasDerivWithinAt",
          "DifferentiableWithinAt", "derivWithin", "MonotoneOn", "AntitoneOn", "StrictMonoOn", "StrictAntiOn"}


def _domain_use(toks, q, m):
    """the interval `toks[q] a S` (S at m) is used only as a domain: the set of a membership binder
    `∈ Icc a S` followed by `,` / `)` / `→`, or a parenthesised set argument `(Icc a S)` of a
    within-/on-predicate (`HasDerivWithinAt f f' (Icc 0 S) x`). Not an operand of `=`, `⊆`, `sSup`, … (an
    interval compared or measured pins S; adversary, run 1428Z)."""
    nxt = toks[m + 1] if m + 1 < len(toks) else None
    if q > 0 and toks[q - 1] == "∈":
        return nxt in (",", ")", "→")
    if q == 0 or toks[q - 1] != "(" or nxt != ")":
        return False
    j, steps = q - 2, 0
    while j >= 0 and steps < 8:
        t = toks[j]
        if t in WITHIN or t.split(".")[-1] in WITHIN:
            return True
        if t in CLOSE:  # skip a bracketed argument backwards
            d = 0
            while j >= 0:
                if toks[j] in CLOSE:
                    d += 1
                elif toks[j] in OPEN:
                    d -= 1
                    if d == 0:
                        break
                j -= 1
        elif t in OPEN or t in RELS or t in ("≠", ",", "∧", "→", "↔", "∨", ":", "+", "-", "*", "/", "^", "⊆", "=") \
                or is_num(t):
            return False
        j -= 1
        steps += 1
    return False


def domain_ends(toks, hi, ok):
    """(a5), run 2026-11-06T1428Z: `c` in a top-level hypothesis binder `(h : c ≤ S)` is a number the proof
    certifies, not data it assumes, when S is a top-level explicit binder `(… S … : ℝ)` and every other
    occurrence of S in the statement is the right end of an interval (`Icc a S`, `Ioc a S`, `Ico a S`,
    `Ioo a S`, `Set.…`), and this is the only binder group that bounds S. Then every instance of the theorem
    (one S) is a statement that does not contain c; c only selects the ray of instances [c, ∞) that the proof
    covers. A source number placed there cannot change what any instance says (contrast a coefficient, or an
    end time also used as an evaluation point `y 40`, which stay uncovered). c must be one number."""
    groups, j = [], 0
    while j < hi and toks[j] in OPEN:
        e = group_end(toks, j)
        groups.append((j, e))
        j = e
    real_binders = set()
    for a, b in groups:
        inner = toks[a + 1:b - 1]
        if toks[a] == "(" and ":" in inner and inner[inner.index(":") + 1:] == ["ℝ"]:
            real_binders.update(x for x in inner[:inner.index(":")])
    for a, b in groups:
        inner = toks[a + 1:b - 1]
        if toks[a] != "(" or len(inner) < 5 or inner[1] != ":" or "≤" not in inner:
            continue
        k = inner.index("≤")
        lhs, rhs = inner[2:k], inner[k + 1:]
        if len(rhs) != 1 or rhs[0] not in real_binders or not _one_num(lhs):
            continue
        S = rhs[0]
        pos = a + 1 + k + 1  # index of S in this binder
        fine = True
        for m, tok in enumerate(toks):
            bare = tok.replace("«", "").replace("»", "")
            if m == pos or not (bare == S or bare.startswith(S + ".") or bare.endswith("." + S)):
                continue
            if tok != S:  # `«S»`, `S.toNNReal`, `x.S`: another spelling of S (adversary, run 1428Z)
                fine = False
                break
            if any(x <= m < y for x, y in groups if (x, y) != (a, b) and toks[x] == "(" and ":" in toks[x + 1:y - 1]
                   and toks[x + 1:y - 1][toks[x + 1:y - 1].index(":") + 1:] == ["ℝ"] and m < x + 1 + toks[x + 1:y - 1].index(":")):
                continue  # S's own declaration `(S : ℝ)`
            if not any(toks[q] in SETS and group_end(toks, q + 1) == m and _domain_use(toks, q, m)
                       for q in range(max(0, m - 12), m - 1)):
                fine = False
                break
        if fine:
            for q in range(a + 1 + 2, a + 1 + k):
                if is_num(toks[q]):
                    ok[q] = "a5"


def zero_one_sides(toks, lo, hi, ok):
    """(a3): `0`/`1` alone as a side of a comparison, anywhere"""
    rel = RELS | {"≠"}
    for j in range(lo, hi):
        if toks[j] in ("0", "1"):
            before = toks[j - 1] if j > lo else None
            after = toks[j + 1] if j + 1 < hi else None
            if after in rel and before in (None, "(", ",", "∧", "→", ":", "↔", "∨", "¬") \
                    or before in rel and after in (None, ")", ",", "∧", "→", "↔", "∨", ":="):
                ok[j] = "a3"


def positive(toks, lo, hi, ok):
    while lo < hi and toks[lo] in OPEN and group_end(toks, lo) == hi and toks[lo] == "(":
        lo, hi = lo + 1, hi - 1
    if lo >= hi:
        return
    if toks[lo] in ("∀", "∃", "∃!"):
        # binder part up to the top-level comma is a hypothesis region
        parts = split_top(toks, lo, hi, {","})
        if len(parts) < 2:
            return
        positive(toks, parts[0][1] + 1, hi, ok)
        return
    if toks[lo] == "¬":
        return
    imp = split_top(toks, lo, hi, {"→"})
    if len(imp) > 1:
        positive(toks, imp[-1][0], imp[-1][1], ok)
        return
    if len(split_top(toks, lo, hi, {"↔", "∨"})) > 1:
        return
    conj = split_top(toks, lo, hi, {"∧"})
    if len(conj) > 1:
        for a, b in conj:
            positive(toks, a, b, ok)
        return
    # atomic proposition
    if toks[lo] in ("RoundsTo", "Checked.Records.RoundsTo", "Records.RoundsTo"):
        args, j = [], lo + 1
        while j < hi:
            e = group_end(toks, j)
            args.append((j, e))
            j = e
        for a, b in args[-2:]:
            if b - a == 1 and is_num(toks[a]):
                ok[a] = "a1"
            # a negative certified decimal `(-0.55)` is the same target (repair, run 2026-11-08T0628Z: every
            # negative RoundsTo value had been baselined as an uncovered literal)
            elif b - a == 4 and toks[a] == "(" and toks[a + 1] in ("-", "−") and is_num(toks[a + 2]) and toks[a + 3] == ")":
                ok[a + 2] = "a1"
        return
    sides = split_top(toks, lo, hi, RELS)
    if len(sides) < 2 or any(t == "≠" for t in toks[lo:hi]):
        return
    # `k = 0.480 + 1.574` with k a bare variable (bound by an enclosing ∃) defines k: data, not a target
    if any(t == "=" for t in toks[lo:hi]) and any(b - a == 1 and not is_num(toks[a]) for a, b in sides):
        return
    for a, b in sides:
        seg = toks[a:b]
        if seg and all(is_num(t) or t in ARITH or t in SETS or t in TYPES or t == ":" for t in seg) and any(is_num(t) for t in seg):
            for j in range(a, b):
                if is_num(toks[j]):
                    ok[j] = "a2"


def pinned_args(toks, row, ok):
    """(a4): numerals passed to a pinned definition with that value recorded in `fixed`"""
    pinned = {p.split(".")[-1] for p in row.get("pinned", [])}
    fixed = {}
    for f in row.get("fixed", []):
        fixed.setdefault(f["def"], set()).add(f["lit"])
    for j, t in enumerate(toks):
        short = t.split(".")[-1]
        if short in pinned and short in fixed:
            k = j + 1
            while k < len(toks) and toks[k] not in CLOSE and toks[k] not in RELS and toks[k] not in (",", "∧", "→"):
                e = group_end(toks, k)
                if e - k == 1 and is_num(toks[k]) and toks[k] in fixed[short]:
                    ok.setdefault(k, "a4")
                k = e


# ------------------------------------------------------------------ readings
def reader_modules():
    gen = set(P.GENERATED)
    return [p for p in sorted((ROOT / "Checked/Trust").glob("SecondReading*.lean")) if p.name not in gen]


def reader_constants():
    """full name -> (binders, body tokens, module rel)"""
    out = {}
    for p in reader_modules():
        text = p.read_text()
        clean = P.strip_comments(text)
        decls, _ = P.declarations(text)
        for full, pos, _ in decls:
            seg = clean[pos:]
            m = re.match(r"[^\n]*?\b(?:def|abbrev)\s+\S+", seg)
            if not m:
                continue
            m2 = re.search(r"\n[ \t]*\n", seg)
            seg = seg[: m2.start()] if m2 else seg
            nxt = P.DECL.search(seg, 1)
            seg = seg[: nxt.start()] if nxt else seg
            m3 = re.search(r"\n[ \t]*(?:end|namespace|section|open|variable)\b", seg)  # last decl of a namespace
            seg = seg[: m3.start()] if m3 else seg
            head, sep, body = seg[m.end():].partition(":=")
            if not sep:
                continue
            binders = []
            for g in re.findall(r"\(([^():]*):[^()]*\)", head):
                binders += g.split()
            out[full] = (binders, lex(body), str(p.relative_to(ROOT)))
    return out


def match_at(stoks, i, pat, binders, lit=None):
    """end index if pat matches stoks starting at i, else None. If `lit` is a list, the statement positions
    matched by a token of the pattern itself (not by a binder wildcard) are appended to it."""
    j = i
    for t in pat:
        if j >= len(stoks):
            return None
        if t in binders:
            j = group_end(stoks, j)
            continue
        if lit is not None:
            lit.append(j)
        s = stoks[j]
        if is_num(t) and is_num(s):
            if value(t) != value(s):
                return None
        elif t != s and not (t in ("-", "−") and s in ("-", "−")):
            return None
        j += 1
    return j


OPS = {"+", "-", "*", "/", "^", "−", "·"}


def eval_closed(toks):
    """exact value of a closed arithmetic expression (numerals, + - * / ^, parentheses), else None"""
    pos = [0]

    def peek():
        return toks[pos[0]] if pos[0] < len(toks) else None

    def take():
        pos[0] += 1
        return toks[pos[0] - 1]

    def atom():
        t = peek()
        if t is None:
            raise ValueError
        if t in ("-", "−"):
            take()
            return -power()
        if t == "(":
            take()
            v = expr()
            if take() != ")":
                raise ValueError
            return v
        if is_num(t):
            take()
            return value(t)
        raise ValueError

    def power():
        b = atom()
        if peek() == "^":
            take()
            e = power()
            if e.denominator != 1 or abs(e) > 64:
                raise ValueError
            if b == 0 and e < 0:
                raise ValueError
            return b ** int(e)
        return b

    def term():
        v = power()
        while peek() in ("*", "/", "·"):
            op = take()
            w = power()
            if op == "/":
                if w == 0:
                    raise ValueError  # x / 0 = 0 in Lean: never a reading
                v = v / w
            else:
                v = v * w
        return v

    def expr():
        v = term()
        while peek() in ("+", "-", "−"):
            op = take()
            w = term()
            v = v + w if op == "+" else v - w
        return v

    if not toks or any(not (is_num(t) or t in ARITH) for t in toks):
        return None
    try:
        v = expr()
    except (ValueError, ZeroDivisionError, IndexError):
        return None
    return v if pos[0] == len(toks) else None


def closed_values(body):
    """(v,) for a closed arithmetic body, (v1, ..., vn) for a tuple `(e1, ..., en)` of them, else None"""
    v = eval_closed(body)
    if v is not None:
        return (v,)
    if len(body) >= 2 and body[0] == "(" and group_end(body, 0) == len(body):
        parts = split_top(body, 1, len(body) - 1, {","})
        if len(parts) >= 2:
            vals = tuple(eval_closed(body[a:b]) for a, b in parts)
            if all(x is not None for x in vals):
                return vals
    return None


def statement_atoms(stoks):
    """[(start, end, exact value)] of the statement's numeric atoms: a numeral, or a parenthesised closed
    arithmetic group, not itself an operand of a neighbouring operator (a maximal arithmetic span)"""
    out, i = [], 0
    while i < len(stoks):
        t = stoks[i]
        e = None
        if is_num(t):
            e = i + 1
        elif t == "(":
            g = group_end(stoks, i)
            if eval_closed(stoks[i + 1:g - 1]) is not None:
                e = g
        if e is not None:
            before = stoks[i - 1] if i > 0 else None
            after = stoks[e] if e < len(stoks) else None
            if before not in OPS and after not in OPS:
                v = eval_closed(stoks[i:e])
                if v is not None:
                    out.append((i, e, v))
                    i = e
                    continue
        i += 1
    return out


def covered_spans(stoks, const, strict=True):
    """statement positions a reader constant covers, one list per occurrence. strict=False (headlines with a
    line in the grandfathered baseline only): every position of the matched span, as before run
    2026-11-07T0828Z."""
    binders, body, _ = const
    spans = []
    if not body:
        return spans
    for i in range(len(stoks)):
        lit = []
        e = match_at(stoks, i, body, set(binders), lit)
        if e is not None:
            # Only the positions the reader's own tokens matched are covered (run 2026-11-07T0828Z): a literal
            # inside a group matched by a binder wildcard was not read by anyone (`Ioc 0 S` matched
            # `Ioc (0 : ℝ) (68 / 5)` and covered 68 / 5).
            spans.append(lit if strict else list(range(i, e)))
    # Value mode (run 2026-11-06T0628Z): a reader constant without binders whose body is a closed arithmetic
    # expression (or a tuple of them) also covers statement atoms of exactly the same value (a run of
    # consecutive atoms, in order, for a tuple). `4 / 100` reads the `(1 / 25)` of a statement; a closed
    # constant has no operator structure beyond its value, so exact value equality is the whole comparison.
    if not binders:
        vals = closed_values(body)
        if vals is not None:
            atoms = statement_atoms(stoks)
            n = len(vals)
            for k in range(len(atoms) - n + 1):
                run = atoms[k:k + n]
                if all(run[m][1] == run[m + 1][0] for m in range(n - 1)) and \
                        tuple(a[2] for a in run) == vals:
                    spans.append(list(range(run[0][0], run[-1][1])))
    return spans


def entries(path):
    p = ROOT / path
    if not p.exists():
        return None
    return [l.split("#")[0].rstrip() for l in p.read_text().splitlines() if l.split("#")[0].strip()]


def resolve(name, heads):
    hits = [h for h in heads if h == name or h.endswith("." + name)]
    return hits[0] if len(hits) == 1 else None


def load_readings(heads, errors):
    """headline -> [(constant, [source names])]"""
    out = {}
    for l in entries(READINGS) or []:
        ps = l.split()
        h = resolve(ps[0], heads)
        if h is None:
            errors.append(f"rule 3: {READINGS}: {ps[0]} is not exactly one headline")
            continue
        srcs = []
        for q in ps[1:]:
            if q.startswith("source="):
                srcs += [s for s in q[len("source="):].split(",") if s]
        for q in ps[1:]:
            if not q.startswith("source="):
                out.setdefault(h, []).append((q, srcs))
    return out


def load_baseline(heads, errors):
    out = {}
    for l in entries(BASELINE) or []:
        parts = [x.strip() for x in l.split("|")]
        if len(parts) < 3 or not parts[2]:
            errors.append(f"rule 3: {BASELINE}: malformed line (need `headline | literals | reason`): {l[:80]}")
            continue
        h = resolve(parts[0], heads)
        if h is None:
            errors.append(f"rule 3: {BASELINE}: {parts[0]} is not exactly one headline")
            continue
        if parts[1].startswith("hidden:"):
            HIDDEN_BL[h] = parts[1][len("hidden:"):].split()
            continue
        out[h] = parts[1].split()
    return out


HIDDEN_BL = {}


def analyse(row, consts, readings, errors, strict=True):
    """(uncovered literal tokens in order, all literal values, statement tokens)"""
    s = statement_text(row["module"], row["name"])
    if s is None:
        errors.append(f"rule 3: cannot read the statement of {row['name']} in {row['module']}")
        return None, None
    toks = lex(s)
    ok = classify(toks)
    pinned_args(toks, row, ok)
    for c, _ in readings.get(row["name"], []):
        const = consts.get(c)
        if const is None:
            errors.append(f"rule 3: {READINGS}: {c} (for {row['name']}) is not a def of a non-generated "
                          f"Checked/Trust/SecondReading*.lean module")
            continue
        if not any(is_num(t) for t in const[1]):
            errors.append(f"rule 3: {READINGS}: {c} has no numeral in its body (it reads no literal)")
            continue
        spans = covered_spans(toks, const, strict)
        if not spans:
            errors.append(f"rule 1: {row['name']}: the registered reading {c} does not occur in the statement "
                          f"(body with binders as wildcards, numerals by value)")
        for span in spans:
            for j in span:
                if is_num(toks[j]):
                    ok.setdefault(j, "b")
    unc = [t for j, t in enumerate(toks) if is_num(t) and j not in ok]
    vals = {value(t) for t in toks if is_num(t)}
    return unc, vals


_SUFFIX = None
_FILES = {}


def def_literal_values(text, depth=3, seen=None):
    """values of the literals in the source of the program declarations a text names (transitively, by
    unique last-name or qualified-suffix resolution): meaning.jsonl's `nums` also records literals of
    unfolded definitions (`Fin 28` of a table, an abbreviation's coefficients)"""
    global _SUFFIX
    if _SUFFIX is None:
        _SUFFIX = {}
        for full, rel in P.program_index().items():
            parts = full.split(".")
            for k in range(1, len(parts) + 1):
                _SUFFIX.setdefault(".".join(parts[-k:]), set()).add((full, rel))
    seen = set() if seen is None else seen
    out = set()
    if depth == 0:
        return out
    for t in set(lex(text)):
        for full, rel in _SUFFIX.get(t, ()):
            if full in seen:
                continue
            seen.add(full)
            if rel not in _FILES:
                src = (ROOT / rel).read_text()
                _FILES[rel] = (src, P.declarations(src)[0])
            src, decls = _FILES[rel]
            d = P.decl_text(src, full, decls) or ""
            out |= {value(x) for x in lex(d) if is_num(x)}
            out |= def_literal_values(d, depth - 1, seen)
    return out


def source_ok(const_rel, names):
    """every registered source name occurs in a brief of the run folder of the module's runs/ copy"""
    copies = P.runs_copies(P.code((ROOT / const_rel).read_text()))
    briefs = ""
    for c in copies:
        run_dir = ROOT / "/".join(c.split("/")[:2])
        for f in run_dir.rglob("*"):
            if f.is_file() and re.search(r"brief", f.name, re.I) and f.suffix == ".md":
                briefs += f.read_text(errors="replace")
    return [n for n in names if n not in briefs]


def load_rows():
    if not MEANING.exists():
        return None
    return [json.loads(l) for l in MEANING.read_text().splitlines() if l.strip()]


def ledger_added(base):
    return P.ledger_added(base)


def main():
    base = sys.argv[sys.argv.index("--base") + 1] if "--base" in sys.argv else None
    report = "--report" in sys.argv
    rows = load_rows()
    if rows is None:
        print(f"check_literals: {MEANING} missing (run scripts/trust/StatementDeps.lean first)")
        return 0 if report else 1
    heads = {r["name"]: r for r in rows if r.get("type") == "headline"}
    errors = []
    for l in entries("scripts/trust/headlines.txt") or []:
        if resolve(l.split()[0], heads) is None:
            errors.append(f"rule 3: headline {l.split()[0]} has no record in {MEANING} (stale: run StatementDeps.lean)")
    consts = reader_constants()
    readings = load_readings(heads, errors)
    baseline = load_baseline(heads, errors)
    for h, regs in readings.items():
        for c, srcs in regs:
            if c in consts and srcs:
                miss = source_ok(consts[c][2], srcs)
                if miss:
                    errors.append(f"rule 1: {READINGS}: source {miss} of {c} is named in no brief of the run "
                                  f"folder of {consts[c][2]}'s runs/ copy")
    n_unc = 0
    for name in sorted(heads):
        row = heads[name]
        unc, vals = analyse(row, consts, readings, errors, strict=row["name"] not in baseline)
        if unc is None:
            continue
        vals |= def_literal_values(statement_text(row["module"], row["name"]) or "")
        # meaning.jsonl records a quotient `a / b` of two literals, and negations, as numbers of their own
        derived = vals | {a / b for a in vals for b in vals if b}
        derived |= {-v for v in derived}
        hidden = sorted({Fraction(x) for x in row.get("nums", [])} - derived - {Fraction(0), Fraction(1)})
        if hidden and HIDDEN_BL.get(name) != [str(x) for x in hidden]:
            errors.append(f"rule 2: {name}: the elaborated statement contains {[str(x) for x in hidden]}, "
                          f"which no literal of its source text has (notation/macro/instance)")
        if report and unc:
            print(f"{name} | {' '.join(unc)}")
        if not unc:
            if name in baseline:
                errors.append(f"rule 1: {BASELINE}: {name} has no uncovered literal any more; remove its line "
                              f"(the baseline only shrinks)")
            continue
        n_unc += 1
        if baseline.get(name) != unc:
            have = baseline.get(name)
            errors.append(f"rule 1: {name}: statement literals {unc} are neither certified targets nor covered by "
                          f"a registered reading ({READINGS})"
                          + (f"; baseline lists {have}" if have is not None else "") +
                          " — enter source data through a PRINTED definition or a blind reader's constant")
    if base:
        old = P.git("show", f"{base}:{BASELINE}")
        if old is not None:
            old_l = {re.sub(r"\s+", " ", "|".join(x.strip() for x in l.split("#")[0].split("|")[:2]))
                     for l in old.splitlines() if l.split("#")[0].strip()}
            old_lists = {}
            for k in old_l:
                h, _, lits = k.partition("|")
                old_lists.setdefault(h.strip(), []).append(lits.split())
            for l in entries(BASELINE) or []:
                key = re.sub(r"\s+", " ", "|".join(x.strip() for x in l.split("|")[:2]))
                if key in old_l:
                    continue
                # A line may shrink: its literal list may lose literals (now covered by a registered reading),
                # keeping the order of the rest (a subsequence of the base line's list, same headline and kind).
                h, _, lits = key.partition("|")
                new_l = lits.split()
                if any(is_subseq(new_l, ol) and len(new_l) < len(ol) and (new_l[:1] == ["hidden:"]) == (ol[:1] == ["hidden:"])
                       for ol in old_lists.get(h.strip(), [])):
                    continue
                errors.append(f"rule 4: {BASELINE} grew or changed against {base}: {key[:100]} (it may only shrink)")
        oldr = P.git("show", f"{base}:{READINGS}")
        if oldr is not None:
            added = set(entries(READINGS) or []) - {l.split("#")[0].rstrip() for l in oldr.splitlines()}
            led = ledger_added(base)
            for l in sorted(added):
                short = l.split()[0].split(".")[-1]
                if short not in led:
                    errors.append(f"rule 4: {READINGS}: added/changed line for {short} without a LEDGER.md addition naming it")
    if report:
        print(f"check_literals: {n_unc} headlines with uncovered literals (report only)")
        return 0
    for e in errors:
        print(e)
    print(f"check_literals: {len(heads)} headlines, {n_unc} with uncovered literals "
          f"({len(baseline)} baselined), {sum(len(v) for v in readings.values())} registered readings; "
          f"{'FAIL' if errors else 'ok'}")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
