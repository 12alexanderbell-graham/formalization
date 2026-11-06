#!/usr/bin/env python3
"""A reader's brief may not hand over the answer in any mechanically recognisable form (run 2026-11-06T1028Z,
part 3; written blind to red team N). Blocking in CI (needs --base). Extends check_blind_route.py B3.

Why: B3 compares only digit numerals of the reader file with digit numerals of the brief. A brief can still
give the answer as words ("one point eight four five"), as split digits ("1 8 4 5", "1-845", "9,999,999"),
as scientific notation ("10^11", "3·10⁷", "1e11"), or as a fragment of a long printed number.

  python3 scripts/trust/check_brief_leak.py --base SHA    every reader file new since SHA (as check_blind_route.py)
  python3 scripts/trust/check_brief_leak.py --all         every reader folder in runs/ (report, never fails)

For every second-version module (non-generated `Checked/Trust/SecondReading*` / `SecondFormulation*`) added or
changed since SHA whose code-identical runs/ copy is new since SHA, every `*brief*.md` in that copy's directory
is read (all of them, not only the first that passes B1). Answer values are: every numeral of the reader file's
code with three or more significant digits or a decimal point, every quotient `a / b` with a multi-digit operand
(as B3), and the exact value of every closed constant body (`10 ^ 11`, `3 * 10 ^ 7`, `4 / 100`; check_literals'
value-mode constants) other than an integer of absolute value below 10.

L1 (words): English number words in the brief (`zero` … `nineteen`, tens, `hundred`, `thousand`, `million`,
   `billion`, `trillion`, `point` + digit words, `minus`/`negative`, hyphenated `forty-two`, and "X to the
   (power of) Y" / ordinal "ten to the eleventh") are converted to values; none may equal an answer value,
   and their digit strings are fed to L3.
L2 (split digits and notation): digit groups joined by at most two separator characters (spaces, commas,
   hyphens, underscores, apostrophes, periods, middle dots, thin spaces; not newlines) are read as one digit
   string ("1 845", "9,999,999", "1-8-4-5"); `a × 10^b`, `a·10^b`, `a*10^b`, `10^b`, `10⁻⁸` (superscripts),
   `aEb` are evaluated. No such value may equal an answer value.
L3 (fragments): no substring of three or more digits of a reader numeral's significant digits (leading zeros
   and the decimal point removed) occurs in any digit string of the brief (L1 and L2 strings, separators
   removed). Trivial fragments are skipped: one repeated digit (`999`, `000`) and a digit followed only by
   zeros (`100`, `3000`), which occur in any text with round numbers.

What remains uncheckable (recorded): formulas that compute the answer ("the coefficient is the square of
0.7 plus …"), the answer named by reference ("use the value of Table 2 row 3 of <program file>"), numbers in
other languages or Roman numerals, units conversions, a brief that points the reader to a file holding the
answer, and anything said to the reader outside the committed brief.
"""
import re
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_provenance as P  # noqa: E402
import check_literals as L  # noqa: E402
import check_blind_route as B  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]

UNITS = {w: i for i, w in enumerate("zero one two three four five six seven eight nine ten eleven twelve thirteen "
                                    "fourteen fifteen sixteen seventeen eighteen nineteen".split())}
TENS = {w: 10 * (i + 2) for i, w in enumerate("twenty thirty forty fifty sixty seventy eighty ninety".split())}
SCALES = {"hundred": 100, "thousand": 10 ** 3, "million": 10 ** 6, "billion": 10 ** 9, "trillion": 10 ** 12}
ORD = {"first": 1, "second": 2, "third": 3, "fourth": 4, "fifth": 5, "sixth": 6, "seventh": 7, "eighth": 8,
       "ninth": 9, "tenth": 10, "eleventh": 11, "twelfth": 12, "thirteenth": 13, "fourteenth": 14, "fifteenth": 15,
       "sixteenth": 16, "seventeenth": 17, "eighteenth": 18, "nineteenth": 19, "twentieth": 20}
NUMWORDS = set(UNITS) | set(TENS) | set(SCALES) | {"point", "minus", "negative", "and", "oh"}
SUPER = str.maketrans("⁰¹²³⁴⁵⁶⁷⁸⁹⁻⁺", "0123456789-+")


def words_to_numbers(text):
    """[(value, digit string)] of the English number phrases of text"""
    toks = re.findall(r"[a-z]+|\d+(?:\.\d+)?", text.lower().replace("-", " "))
    out, i = [], 0
    while i < len(toks):
        if toks[i] not in NUMWORDS or toks[i] in ("and", "point", "oh"):
            i += 1
            continue
        sign, j = 1, i
        if toks[j] in ("minus", "negative"):
            sign, j = -1, j + 1
        total, cur, seen, digits = 0, 0, False, ""
        while j < len(toks):
            t = toks[j]
            if t in UNITS:
                cur += UNITS[t]
                digits += str(UNITS[t])
            elif t in TENS:
                cur += TENS[t]
                digits += str(TENS[t] // 10)
            elif t in SCALES:
                if SCALES[t] == 100:
                    cur = max(cur, 1) * 100
                else:
                    total += max(cur, 1) * SCALES[t]
                    cur = 0
            elif t == "and" and seen and j + 1 < len(toks) and (toks[j + 1] in UNITS or toks[j + 1] in TENS):
                pass
            else:
                break
            seen = True
            j += 1
        if not seen:
            i += 1
            continue
        val = Fraction(total + cur)
        if j < len(toks) and toks[j] == "point":
            frac, k = "", j + 1
            while k < len(toks) and (toks[k] in UNITS and UNITS[toks[k]] < 10 or toks[k] == "oh"):
                frac += "0" if toks[k] == "oh" else str(UNITS[toks[k]])
                k += 1
            if frac:
                val += Fraction(int(frac), 10 ** len(frac))
                digits += frac
                j = k
        # "X to the (power of) Y" / "X to the Yth"
        if j + 2 < len(toks) and toks[j] == "to" and toks[j + 1] == "the":
            k = j + 2
            if k < len(toks) and toks[k] == "power":
                k += 1
                if k < len(toks) and toks[k] == "of":
                    k += 1
            esign = 1
            if k < len(toks) and toks[k] in ("minus", "negative"):
                esign, k = -1, k + 1
            e = None
            if k < len(toks):
                if toks[k] in ORD:
                    e = ORD[toks[k]]
                elif toks[k] in UNITS:
                    e = UNITS[toks[k]]
                elif toks[k] in TENS:
                    e = TENS[toks[k]]
                    if k + 1 < len(toks) and toks[k + 1] in ORD:
                        e += ORD[toks[k + 1]]
                elif toks[k].isdigit():
                    e = int(toks[k])
            if e is not None and abs(e) <= 64:
                out.append((sign * val ** (esign * e) if val else Fraction(0), ""))
        out.append((sign * val, digits))
        i = max(j, i + 1)
    return out


def digit_strings(text):
    """[(value or None, digits)] of digit groups joined by at most two separator characters, plus notation"""
    out = []
    t = text.translate(SUPER)
    for m in re.finditer(r"\d(?:[ \t,\-_'’.·   ]{0,2}\d)*", t):
        s = m.group(0)
        digits = re.sub(r"\D", "", s)
        val = None
        if re.fullmatch(r"\d+(?:\.\d+)?", s):
            val = Fraction(s)
        out.append((val, digits))
    for m in re.finditer(r"(?:(\d+(?:\.\d+)?)\s*[×x·*⋅]\s*)?10\s*(?:\^|\*\*)\s*\(?\s*([-−+]?\s*\d+)\s*\)?", t):
        mant = Fraction(m.group(1)) if m.group(1) else Fraction(1)
        e = int(m.group(2).replace("−", "-").replace(" ", ""))
        if abs(e) <= 64:
            out.append((mant * Fraction(10) ** e, ""))
    for m in re.finditer(r"(?<![\w.])(\d+(?:\.\d+)?)[eE]([-+]?\d+)(?!\w)", t):
        e = int(m.group(2))
        if abs(e) <= 64:
            out.append((Fraction(m.group(1)) * Fraction(10) ** e, ""))
    return out


def sig_digits(numeral):
    return numeral.replace(".", "").lstrip("0")


def trivial(frag):
    return len(set(frag)) == 1 or (frag[0] != "0" and set(frag[1:]) == {"0"})


def answer(code):
    """(answer values, significant digit strings of the reader's numerals)"""
    vals = set(B.answer_numbers(code))
    for m in re.finditer(r"(?<![\w.])\d+\.\d+(?![\w.])", code):
        vals.add(Fraction(m.group(0)))
    for m in re.finditer(r"(?<![\w.])\d{3,}(?![\w.])", code):
        vals.add(Fraction(m.group(0)))
    for line in code.splitlines():
        m = re.search(r"\bdef\s+\S+\s*(?:\([^)]*\))?\s*(?::[^=]*)?:=\s*(.+)$", line)
        if m and not re.search(r"\bdef\s+\S+\s*\(", line):
            cv = L.closed_values(L.lex(m.group(1)))
            for v in cv or ():
                if not (v.denominator == 1 and abs(v) < 10):
                    vals.add(v)
    digs = {sig_digits(x) for x in re.findall(r"(?<![\w.])\d+(?:\.\d+)?(?![\w.])", code)}
    return vals, {d for d in digs if len(d) >= 3}


def leaks(code, text):
    vals, digs = answer(code)
    found = []
    strings = digit_strings(text) + words_to_numbers(text)
    for v, d in strings:
        if v is not None and v in vals:
            found.append(f"value {v} ({float(v):.12g})")
    frags = set()
    for d in digs:
        for a in range(len(d)):
            for b in range(a + 3, len(d) + 1):
                if not trivial(d[a:b]):
                    frags.add(d[a:b])
    for v, d in strings:
        if len(d) >= 3:
            hit = [f for f in frags if f in d]
            if hit:
                found.append(f"digits {max(hit, key=len)!r} inside {d!r}")
    return sorted(set(found))


def reader_routes(base):
    """[(module rel, runs copy, [briefs])] of second versions with a reader file new since base"""
    out = []
    for rel in P.all_lean():
        if not P.second_module(rel) or Path(rel).name in P.GENERATED:
            continue
        if base and P.git("show", f"{base}:{rel}") == (ROOT / rel).read_text():
            continue
        code = P.code((ROOT / rel).read_text())
        for c in P.runs_copies(code):
            if base and P.git("cat-file", "-e", f"{base}:{c}") is not None:
                continue
            out.append((rel, c, B.briefs_for(c)))
    return out


def main():
    if "--all" in sys.argv:
        for rel, c, bs in reader_routes(None):
            code = P.code((ROOT / c).read_text())
            for b in bs:
                f = leaks(code, (ROOT / b).read_text(errors="replace"))
                print(f"{b}: {'; '.join(f) if f else 'clean'}")
        return 0
    if "--base" not in sys.argv:
        print("check_brief_leak: needs --base SHA (or --all to report every reader folder)")
        return 0
    base = sys.argv[sys.argv.index("--base") + 1]
    if P.git("cat-file", "-e", f"{base}^{{commit}}") is None:
        print(f"check_brief_leak: base {base} not available; skipped")
        return 0
    errors, n = [], 0
    for rel, c, bs in reader_routes(base):
        code = P.code((ROOT / c).read_text())
        for b in bs:
            n += 1
            f = leaks(code, (ROOT / b).read_text(errors="replace"))
            if f:
                errors.append(f"{rel}: brief {b} hands over the reader's answer: {'; '.join(f[:6])}")
    for e in errors:
        print(e)
    print(f"check_brief_leak: {n} briefs of reader files new since {base[:12]}; {'FAIL' if errors else 'ok'}")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
