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
TAG = r"\[(✓[A-Za-z0-9_]+|in✓[A-Za-z0-9_]+|src|in|unc)\]"
PARAMS = ".lake/records_params.tsv"


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


def scope(text):
    i = text.find("\n" + UNVERIFIED)
    if i < 0:
        return text
    j = text.find("\n## ", i + 1)
    return text[:i] + ("\n" + text[j:] if j >= 0 else "")


def code_blank(line):
    return re.sub(r"`[^`]*`", lambda mm: " " * len(mm.group()), line)


def certified_pairs(text):
    out = {}
    for line in scope(text).split("\n"):
        for t in re.finditer(r"(" + NUM + r")\[((?:in)?✓[A-Za-z0-9_]+)\]", code_blank(line)):
            k = (norm(t.group(1)), t.group(2))
            out[k] = out.get(k, 0) + 1
    return out


def base_check(base):
    # a new branch has no "before" commit (all zeros): compare with the parent, as check_relock.py does
    if not base or set(base) == {"0"} or subprocess.run(
            ["git", "cat-file", "-e", base + "^{commit}"], capture_output=True).returncode:
        base = "HEAD~1"
    old = subprocess.run(["git", "show", f"{base}:{FINDINGS}"], capture_output=True, text=True)
    if old.returncode != 0:
        print(f"certified-number diff: no {FINDINGS} at {base}; skipped")
        return 0
    before = certified_pairs(old.stdout)
    after = certified_pairs(open(FINDINGS, encoding="utf-8").read())
    lost = [k for k, c in before.items() if after.get(k, 0) < c]
    led = subprocess.run(["git", "diff", base, "HEAD", "--", "LEDGER.md"], capture_output=True, text=True).stdout
    added = "\n".join(l[1:] for l in led.splitlines() if l.startswith("+") and not l.startswith("+++"))
    missing = [k for k in lost if not re.search(r"(?<![\w.])" + re.escape(k[1].split("✓")[-1]) + r"(?![\w])", added)]
    print(f"certified-number diff vs {base}: {len(before)} certified pairs before, {len(after)} now, "
          f"{len(lost)} removed or changed")
    for num, name in missing:
        name = name.replace("in✓", "").replace("✓", "")
        print(f"::error::certified number {num}[✓{name}] was changed, removed or downgraded without a "
              f"LEDGER.md entry naming {name}")
    return 1 if missing else 0


def main():
    if len(sys.argv) == 3 and sys.argv[1] == "--base":
        return base_check(sys.argv[2])
    try:
        rows = [l.split("\t") for l in open(TSV, encoding="utf-8").read().splitlines() if l.strip()]
    except FileNotFoundError:
        print(f"::error::{TSV} missing: run `lake env lean scripts/trust/StatementDeps.lean` first")
        return 1
    cert = {}
    for name, val in rows:
        cert.setdefault(name, []).append(val)
    params = {}
    try:
        for l in open(PARAMS, encoding="utf-8").read().splitlines():
            if l.strip():
                name, fr = l.split("\t")
                params.setdefault(name, set()).add(Fraction(fr))
    except FileNotFoundError:
        pass
    text = open(FINDINGS, encoding="utf-8").read()
    if "## Verified findings" not in text:
        print("::error::FINDINGS.md has no '## Verified findings' section")
        return 1
    errors, counts = [], {"✓": 0, "src": 0, "in": 0, "unc": 0}
    for line in scope(text).split("\n"):
        s = code_blank(line)
        tagged_starts = set()
        for t in re.finditer(r"(" + NUM + r")" + TAG, s):
            num, tag = t.group(1), t.group(2)
            tagged_starts.add(t.start(1))
            if tag.startswith("in✓"):
                name = tag[3:]
                v, _ = value(num)
                if Fraction(v) not in params.get(name, set()):
                    errors.append(f"{num}[{tag}]: {name} is not stated at {num} (its parameters: "
                                  f"{sorted(str(x) for x in params.get(name, set()))[:12]})")
                else:
                    counts["in"] += 1
            elif tag.startswith("✓"):
                name = tag[1:]
                if name not in cert:
                    errors.append(f"[✓{name}] after {num}: no registered Checked.Records headline {name} asserts a RoundsTo")
                elif value(num) not in [value(v) for v in cert[name]]:
                    errors.append(f"{num}[✓{name}]: {name} certifies {cert[name]}, not {num}")
                else:
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
        for t in re.finditer(r"\[(✓[^\]]*|in✓[^\]]*|src|in|unc)\]", s):
            if not any(re.match(NUM + r"$", s[a:t.start()]) for a in tagged_starts if a < t.start()):
                errors.append(f"tag {t.group()} not directly after a number: {line.strip()[:80]}")
        for t in re.finditer(r"(?<![\w.])(" + NUM + r")(?!\d)(?!\.\d)", s):
            a, b = t.span(1)
            num = t.group(1)
            is_dec = "." in num or "×10" in num
            approx = s[:a].rstrip().endswith(("≈", "≃"))
            if not (is_dec or approx) or a in tagged_starts:
                continue
            if s[a - 1:a] == "(" and s[b:b + 1] == ")":
                continue  # equation number
            if re.fullmatch(r"\d{4}\.\d{4,5}", num):
                continue  # arXiv identifier
            errors.append(f"untagged number {num}: …{s[max(0, a - 50):b + 15].strip()}…")
    total = sum(counts.values())
    print(f"certified numbers (FINDINGS.md outside '{UNVERIFIED}'): {counts['✓']} certified [✓], "
          f"{counts['src']} quoted [src], {counts['in']} inputs [in], {counts['unc']} unchecked [unc]; "
          f"{total} tagged")
    for e in errors:
        print(f"::error::{e}")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
