#!/usr/bin/env python3
"""Certified targets hold one number, and value-mode readings cover only the slots they are registered for
(run 2026-11-06T1028Z, part 3; check-writer blind to red team N's files, brief written after its report). Blocking in CI; reads .lake/meaning.jsonl.

Why: check_literals.py (round M) exempts (a2) every literal of an all-numeral side of a comparison in the
conclusion, as "the side the proof certifies". A source number put there is never read twice: a printed
value, a coefficient, or a correlation evaluated at a point compared with a weak or trivial bound
(`2 < 0.480 + 1.574 * 1 + 0.176 * 1 ^ 2`) passes as a "target". And its value mode (run 0628Z) lets a closed
reader constant cover ANY atom of equal value: `robT := 40` covers a `40` used as a time inside `y₂ 40` and
as a bound elsewhere; `robInit := (1, 0, 0)` any run `1 0 0`. This script re-classifies every literal that
check_literals.py exempts by (a2) or covers by a binder-free closed reader constant, under two stricter
rules; check_literals.py keeps enforcing everything else (it is not changed).

  python3 scripts/trust/check_literal_targets.py              rules T1-T3 on the current tree
  python3 scripts/trust/check_literal_targets.py --base SHA   also T4 (baseline shrink-only, slot registry disclosed)
  python3 scripts/trust/check_literal_targets.py --report     print every headline's extra literals, never fail

T1 (one-number targets; closes the a2 limit): a side of `= ≤ < ≥ >` or `∈` in a positive position of the
   conclusion is a certified target only if it is ONE number: a numeral, a decimal, a quotient `a / b` of two
   numerals, scientific notation `m * 10 ^ k`, `m / 10 ^ k`, `10 ^ k` (k a numeral or a negated numeral), with
   optional sign, parentheses and type ascriptions; or `Set.Icc/Ico/Ioc/Ioo e₁ e₂` with each end one number
   (an interval's two ends). A side that does arithmetic over several source numbers is data, not a target:
   its literals need a reading. Exception inside a target side: additive terms (top-level `+`/`-` terms)
   covered by a reader constant registered with the slot `target` (T2) are taken out first; what remains
   must then be at most one number (`printedY3 + 1 / 10 ^ 14 < y₃ T`: the printed term read, the margin
   is the target).
T2 (position-bound value mode; closes the run-0628Z limit): a binder-free reader constant whose body is a
   closed arithmetic expression or a tuple of them (exactly the constants check_literals.py compares by
   value) covers a statement literal only at a slot registered for it in `scripts/trust/literal_slots.txt`
   (`<reader constant> <slot> [<slot> ...]`):
     `<Def>.<param>`  the literal is the explicit argument `<param>` of a call of the program definition
                      `<Def>` (short name) that the statement reaches (meaning.jsonl `defs`/`pinned`); the
                      argument index comes from `<Def>`'s explicit binders in its source, and the value must
                      also be recorded for that definition and parameter in meaning.jsonl `fixed` (the
                      elaborated statement): `robT IsRobSolution.T` covers the `40` passed as T, not the
                      `40` of `y₂ 40` or a bound `y < 40`. A tuple constant lists one slot per component,
                      all filled in the same call (`robInit IsRobSolution.a₀ IsRobSolution.b₀ IsRobSolution.c₀`).
     `target`         an additive term of a certified target side (T1) of exactly the constant's value.
     `<Def>.<param>+eval`  as `<Def>.<param>`, and also the argument of every application `f n` of a function
                      `f` passed as a single-identifier argument to that same call, when n has the constant's
                      value (run 2026-11-06T1028Z: `y₁ 40` beside `IsRobSolution … 40 y₁ y₂ y₃` is the solution
                      evaluated at the end time the reader read; an evaluation at another time is not covered).
   A closed constant without a slot line covers nothing here. Constants with binders (formulas) keep
   check_literals.py's token match (operators and signs compared), and binder-free constants whose body is
   not closed arithmetic keep it too.
T3 (exact baseline): for every headline, the "extra" literals — exempt or covered under check_literals.py
   but not under T1/T2 — must equal, in statement order, its line in the shrink-only
   `scripts/trust/literal_target_baseline.txt` (`<headline> | <extra literals> | <reason>`), populated from
   the tree at 6fc653c. A new headline has no line; a changed statement fires again. A registered slot that
   covers nothing in a headline its constant is registered for fails (stale or wrong slot).
T4 (--base): the baseline may only shrink (a line may lose literals, keeping the order of the rest); a line
   added to or changed in literal_slots.txt needs a LEDGER.md addition naming the constant's last name
   component.

Limits: the slot says WHERE a reading may count, not that the reader meant that slot (the slot line is the
author's; its LEDGER disclosure is the evidence); `target` terms are compared by value; one number on a
target side is still exempt, so a single printed number compared with a weak bound (`1 < 0.37464`) passes
here as before (it is a one-number target; check_source_names/prose read what the docstring claims of it).
"""
import re
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_provenance as P  # noqa: E402
import check_literals as L  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]
SLOTS = "scripts/trust/literal_slots.txt"
BASELINE = "scripts/trust/literal_target_baseline.txt"
NEG = ("-", "−")
STOP = set(L.CLOSE) | L.RELS | {",", "∧", "→", "↔", "∨", ":=", "≠", "+", "-", "−", "*", "/", "^", "·", "|"}


# ------------------------------------------------------------------ T1: one-number sides
def _strip(seg):
    """drop type ascriptions (`: ℝ`) and redundant outer parentheses"""
    out = []
    i = 0
    while i < len(seg):
        if seg[i] == ":" and i + 1 < len(seg) and seg[i + 1] in L.TYPES:
            i += 2
            continue
        out.append(seg[i])
        i += 1
    while len(out) >= 2 and out[0] == "(" and L.group_end(out, 0) == len(out):
        out = out[1:-1]
    return out


def _pow10(s):
    if len(s) < 3 or s[0] != "10" or s[1] != "^":
        return False
    e = _strip(s[2:])
    if e and e[0] in NEG:
        e = e[1:]
    return len(e) == 1 and L.is_num(e[0]) and "." not in e[0]


def one_number(seg):
    """is the token list one number (numeral, decimal, quotient of two numerals, scientific notation)?"""
    s = _strip(list(seg))
    if s and s[0] in NEG:
        s = _strip(s[1:])
    if not s:
        return False
    if len(s) == 1:
        return L.is_num(s[0])
    if _pow10(s):
        return True
    # a power of one number with a numeral exponent (`(5 / 4) ^ 2`: a radius squared)
    e0 = L.group_end(s, 0)
    if e0 + 2 == len(s) and s[e0] == "^" and L.is_num(s[e0 + 1]) and "." not in s[e0 + 1] \
            and (e0 > 1 or L.is_num(s[0])) and one_number(s[:e0]):
        return True
    # m op rest, m a single (possibly parenthesised) numeral group
    e = L.group_end(s, 0)
    head, rest = s[:e], s[e:]
    if not rest or rest[0] not in ("/", "*", "·"):
        return False
    hs = _strip(head)
    if hs and hs[0] in NEG:
        hs = hs[1:]
    if not (len(hs) == 1 and L.is_num(hs[0])):
        return False
    tail = _strip(rest[1:])
    if rest[0] == "/" and len(tail) == 1 and L.is_num(tail[0]):
        return True
    return _pow10(tail)


def additive_terms(toks, a, b):
    """[(lo, hi)] top-level additive terms of toks[a:b] (a leading sign belongs to its term)"""
    parts, d, start = [], 0, a
    for j in range(a, b):
        t = toks[j]
        if t in L.OPEN:
            d += 1
        elif t in L.CLOSE:
            d -= 1
        elif d == 0 and t in ("+", "-", "−") and j > start and toks[j - 1] not in ("^", "*", "/", "(", "·"):
            parts.append((start, j))
            start = j + 1 if t == "+" else j
    parts.append((start, b))
    return [(x, y) for x, y in parts if y > x]


def strict_targets(toks, target_vals):
    """{index: reason} under T1 for the literals that check_literals' (a2) exempts; `target_vals` maps a
    value to the constants registered with slot `target` (their terms count as read)"""
    ok, used = {}, {}
    lo = 0
    n = len(toks)
    while lo < n and toks[lo] in L.OPEN:
        lo = L.group_end(toks, lo)
    if lo < n and toks[lo] == ":":
        lo += 1
    sides = []
    _positive_sides(toks, lo, n, sides)
    for a, b in sides:
        seg = toks[a:b]
        if seg and seg[0] in L.SETS:
            args, j = [], a + 1
            while j < b:
                e = L.group_end(toks, j)
                args.append((j, e))
                j = e
            if args and all(one_number(toks[x:y]) for x, y in args):
                for j in range(a, b):
                    if L.is_num(toks[j]):
                        ok[j] = "T1"
            continue
        rest = []
        for x, y in additive_terms(toks, a, b):
            v = L.eval_closed([t for t in _strip(toks[x:y])] if toks[x] not in NEG else toks[x:y])
            if v is not None and v in target_vals:
                for j in range(x, y):
                    if L.is_num(toks[j]):
                        ok[j] = "T2-target"
                used.setdefault(target_vals[v], 0)
                used[target_vals[v]] += 1
                continue
            rest.append((x, y))
        if not rest:
            continue
        if len(rest) == 1 and one_number(toks[rest[0][0]:rest[0][1]] if toks[rest[0][0]] not in ("+",) else toks[rest[0][0] + 1:rest[0][1]]):
            for j in range(rest[0][0], rest[0][1]):
                if L.is_num(toks[j]):
                    ok[j] = "T1"
    return ok, used


def _positive_sides(toks, lo, hi, out):
    """the all-numeral comparison sides that check_literals.positive exempts by (a2), as index ranges"""
    while lo < hi and toks[lo] in L.OPEN and L.group_end(toks, lo) == hi and toks[lo] == "(":
        lo, hi = lo + 1, hi - 1
    if lo >= hi:
        return
    if toks[lo] in ("∀", "∃", "∃!"):
        parts = L.split_top(toks, lo, hi, {","})
        if len(parts) >= 2:
            _positive_sides(toks, parts[0][1] + 1, hi, out)
        return
    if toks[lo] == "¬":
        return
    imp = L.split_top(toks, lo, hi, {"→"})
    if len(imp) > 1:
        _positive_sides(toks, imp[-1][0], imp[-1][1], out)
        return
    if len(L.split_top(toks, lo, hi, {"↔", "∨"})) > 1:
        return
    conj = L.split_top(toks, lo, hi, {"∧"})
    if len(conj) > 1:
        for a, b in conj:
            _positive_sides(toks, a, b, out)
        return
    if toks[lo] in ("RoundsTo", "Checked.Records.RoundsTo", "Records.RoundsTo"):
        return
    sides = L.split_top(toks, lo, hi, L.RELS)
    if len(sides) < 2 or any(t == "≠" for t in toks[lo:hi]):
        return
    if any(t == "=" for t in toks[lo:hi]) and any(b - a == 1 and not L.is_num(toks[a]) for a, b in sides):
        return
    for a, b in sides:
        seg = toks[a:b]
        if seg and all(L.is_num(t) or t in L.ARITH or t in L.SETS or t in L.TYPES or t == ":" for t in seg) \
                and any(L.is_num(t) for t in seg):
            out.append((a, b))


# ------------------------------------------------------------------ T2: slots
_PARAMS = {}


def explicit_params(full):
    """explicit binder names of a program declaration, in order (None if not found)"""
    if full in _PARAMS:
        return _PARAMS[full]
    rel = P.program_index().get(full)
    res = None
    if rel:
        src = (ROOT / rel).read_text()
        d = P.decl_text(src, full, P.declarations(src)[0])
        if d:
            m = re.match(r"[^\n]*?\b(?:def|abbrev|structure|theorem|lemma)\s+\S+", d)
            head = d[m.end():] if m else ""
            toks = L.lex(head)
            res, i = [], 0
            while i < len(toks):
                t = toks[i]
                if t in (":", ":="):
                    break
                e = L.group_end(toks, i)
                if t == "(":
                    inner = toks[i + 1:e - 1]
                    if ":" in inner:
                        res += [x for x in inner[:inner.index(":")]]
                elif t not in L.OPEN:
                    res = None  # unexpected shape: fail closed
                    break
                i = e
    _PARAMS[full] = res
    return res


def call_args(toks, j):
    """[(lo, hi)] explicit arguments following the function token toks[j]"""
    out, k = [], j + 1
    while k < len(toks) and toks[k] not in STOP and toks[k] not in (":", "∈", "∀", "∃", "∃!", "¬", "fun", "λ"):
        e = L.group_end(toks, k)
        out.append((k, e))
        k = e
    return out


def slot_spans(toks, row, vals, slots):
    """index spans where the closed constant with values `vals` sits at its registered slots"""
    reached = list(row.get("defs", {})) + list(row.get("pinned", []))
    fixed = {}
    for f in row.get("fixed", []):
        try:
            fixed.setdefault((f["def"], f["param"]), set()).add(Fraction(f["lit"]))
        except (ValueError, ZeroDivisionError):
            pass
    dslots = [s for s in slots if s != "target"]
    if not dslots or len(dslots) != len(vals):
        return []
    defs = {s.rsplit(".", 1)[0] for s in dslots}
    if len(defs) != 1:
        return []
    dshort = defs.pop()
    fulls = [d for d in reached if d.split(".")[-1] == dshort]
    if len(fulls) != 1:
        return []
    params = explicit_params(fulls[0])
    if not params:
        return []
    spans = []
    for j, t in enumerate(toks):
        if t.split(".")[-1] != dshort or (j > 0 and toks[j - 1] == "@"):
            continue
        args = call_args(toks, j)
        cov = []
        evals = []
        for s, v in zip(dslots, vals):
            p = s.rsplit(".", 1)[1]
            ev = p.endswith("+eval")
            p = p[:-len("+eval")] if ev else p
            if p not in params or params.index(p) >= len(args):
                cov = None
                break
            lo, hi = args[params.index(p)]
            av = L.eval_closed(toks[lo:hi])
            if av is None or av != v or v not in fixed.get((dshort, p), set()):
                cov = None
                break
            cov.append((lo, hi))
            if ev:
                evals.append(v)
        if cov:
            spans += cov
            # `<Def>.<param>+eval` (run 2026-11-06T1028Z): also the evaluations `f n` at that value of the
            # functions passed to this same call (single identifier arguments, i.e. the statement's solution
            # variables): `y₁ 40` with `IsRobSolution … 40 y₁ y₂ y₃` is the solution at the end time the reader read
            fvars = {toks[lo] for lo, hi in args if hi == lo + 1 and re.match(r"^[^\W\d]", toks[lo])}
            for v in evals:
                for i, u in enumerate(toks):
                    if u in fvars and i + 1 < len(toks) and not (i > 0 and toks[i - 1] == dshort):
                        e = L.group_end(toks, i + 1)
                        if L.eval_closed(toks[i + 1:e]) == v and (i < j or i >= args[-1][1]):
                            spans.append((i + 1, e))
    return spans


def load_slots(errors):
    out = {}
    for l in L.entries(SLOTS) or []:
        ps = l.split()
        if len(ps) < 2:
            errors.append(f"T3: {SLOTS}: malformed line {l[:80]}")
            continue
        out[ps[0]] = ps[1:]
    return out


# ------------------------------------------------------------------ comparison with check_literals
def classify_both(row, consts, readings, slots, errors, strict=True):
    """(statement tokens, old exempt/covered indices, strict indices, slot usage)"""
    s = L.statement_text(row["module"], row["name"])
    if s is None:
        return None
    toks = L.lex(s)
    old = L.classify(toks)
    L.pinned_args(toks, row, old)
    new = {j: r for j, r in old.items() if r != "a2"}
    target_vals, closed = {}, {}
    for c, _ in readings.get(row["name"], []):
        const = consts.get(c)
        if const is None:
            continue
        binders, body, _ = const
        vals = L.closed_values(body) if not binders else None
        for span in L.covered_spans(toks, const, strict):
            for j in span:
                if L.is_num(toks[j]):
                    old.setdefault(j, "b")
        if vals is None:
            for span in L.covered_spans(toks, const, strict):
                for j in span:
                    if L.is_num(toks[j]):
                        new.setdefault(j, "b")
            continue
        closed[c] = vals
        sl = slots.get(c)
        if sl is None:
            continue
        if "target" in sl and len(vals) == 1:
            target_vals[vals[0]] = c
    used = {}
    for c, vals in closed.items():
        sl = slots.get(c, [])
        sp = slot_spans(toks, row, vals, sl)
        if sp:
            used[c] = used.get(c, 0) + 1
        for a, b in sp:
            for j in range(a, b):
                if L.is_num(toks[j]):
                    new.setdefault(j, "T2-slot")
    tok_ok, tused = strict_targets(toks, target_vals)
    for j, r in tok_ok.items():
        new.setdefault(j, r)
    for c, k in tused.items():
        used[c] = used.get(c, 0) + k
    for c in closed:
        sl = slots.get(c)
        if sl and not used.get(c):
            errors.append(f"T3: {row['name']}: reader constant {c} is registered with slots {sl} ({SLOTS}) but "
                          f"covers no literal at them in this statement (wrong or stale slot)")
    return toks, old, new


def main():
    base = sys.argv[sys.argv.index("--base") + 1] if "--base" in sys.argv else None
    report = "--report" in sys.argv
    rows = L.load_rows()
    if rows is None:
        print("check_literal_targets: .lake/meaning.jsonl missing (run StatementDeps.lean first)")
        return 0 if report else 1
    heads = {r["name"]: r for r in rows if r.get("type") == "headline"}
    errors = []
    consts = L.reader_constants()
    readings = L.load_readings(heads, [])
    slots = load_slots(errors)
    for c, sl in slots.items():
        if c not in consts:
            errors.append(f"T3: {SLOTS}: {c} is not a reader constant")
            continue
        if L.closed_values(consts[c][1]) is None or consts[c][0]:
            errors.append(f"T3: {SLOTS}: {c} is not a closed (binder-free arithmetic) constant; slots apply to value mode only")
        for s in sl:
            if s != "target" and not re.fullmatch(r"[^\W\d][\w'₀-₉]*\.[^\W\d][\w'₀-₉]*(\+eval)?", s):
                errors.append(f"T3: {SLOTS}: slot {s!r} of {c} is neither `target` nor `<Def>.<param>`")
    bl = {}
    for l in L.entries(BASELINE) or []:
        ps = [x.strip() for x in l.split("|")]
        if len(ps) < 3 or not ps[2]:
            errors.append(f"T3: {BASELINE}: malformed line {l[:80]}")
            continue
        h = L.resolve(ps[0], heads)
        if h is None:
            errors.append(f"T3: {BASELINE}: {ps[0]} is not exactly one headline")
            continue
        bl[h] = ps[1].split()
    n_extra = 0
    lit_bl = L.load_baseline(heads, [])  # headlines grandfathered in check_literals' baseline: old span rule
    for name in sorted(heads):
        res = classify_both(heads[name], consts, readings, slots, errors, strict=name not in lit_bl)
        if res is None:
            continue
        toks, old, new = res
        extra = [toks[j] for j in sorted(old) if L.is_num(toks[j]) and j not in new]
        if report:
            if extra:
                why = sorted({old[j] for j in old if L.is_num(toks[j]) and j not in new})
                print(f"{name} | {' '.join(extra)} | {why}")
            continue
        if not extra:
            if name in bl:
                errors.append(f"T3: {BASELINE}: {name} has no extra literal any more; remove its line (shrink-only)")
            continue
        n_extra += 1
        if bl.get(name) != extra:
            errors.append(f"T1/T2: {name}: literals {extra} pass check_literals.py only as an arithmetic 'target' side or "
                          f"through a value-mode reading outside its registered slot ({SLOTS})"
                          + (f"; baseline lists {bl[name]}" if name in bl else "")
                          + " — a target side holds one number; register the reader constant's slot or read the data")
    if base:
        old = P.git("show", f"{base}:{BASELINE}")
        if old is not None:
            old_lists = {}
            for l in old.splitlines():
                l = l.split("#")[0]
                if l.strip():
                    ps = [x.strip() for x in l.split("|")]
                    if len(ps) >= 2:
                        old_lists.setdefault(ps[0], []).append(ps[1].split())
            for l in L.entries(BASELINE) or []:
                ps = [x.strip() for x in l.split("|")]
                cur = ps[1].split() if len(ps) > 1 else []
                if not any(cur == ol or (L.is_subseq(cur, ol) and len(cur) < len(ol)) for ol in old_lists.get(ps[0], [])):
                    errors.append(f"T4: {BASELINE} grew or changed against {base}: {l[:100]} (it may only shrink)")
        olds = P.git("show", f"{base}:{SLOTS}")
        if olds is not None:
            prev = {l.split("#")[0].rstrip() for l in olds.splitlines()}
            led = P.ledger_added(base)
            for l in sorted(set(L.entries(SLOTS) or []) - prev):
                short = l.split()[0].split(".")[-1]
                if short not in led:
                    errors.append(f"T4: {SLOTS}: added/changed line for {short} without a LEDGER.md addition naming it")
    if report:
        return 0
    for e in errors:
        print(e)
    print(f"check_literal_targets: {len(heads)} headlines, {n_extra} with extra literals ({len(bl)} baselined), "
          f"{len(slots)} slot registrations; {'FAIL' if errors else 'ok'}")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
