#!/usr/bin/env python3
"""Certified numbers in the records (trust track T4/T5, run 2026-10-31T0228Z). Blocking in CI.

Red-team defects A06 and B07 (run 2026-10-31T0028Z) changed numbers in FINDINGS.md and every
check accepted them. Rule: every number in the "Verified findings" section of FINDINGS.md that
is a decimal (or follows ≈/≃) carries a tag right after it:

  [✓name]  certified: `Checked.Records.name` is a registered headline whose statement contains
           `RoundsTo x d k` with `d` written with `k` decimals exactly as in the prose
           (literals extracted by scripts/trust/StatementDeps.lean into .lake/records_numbers.tsv);
  [src]    quoted from the source (a number printed in the paper);
  [in]     an input chosen for illustration (a parameter value), not a result;
  [unc]    computed but NOT machine-checked (the reader sees that it is unchecked).

With `--base REF` (CI, after the frozen-registry check) it also compares with REF: a certified
pair (number, [✓name]) present at REF and absent now (number changed, or tag downgraded to
[src]/[in]/[unc]) needs a LEDGER.md line added since REF naming `name` (as frozen entries do).

Not numbers for this rule: arXiv identifiers, equation numbers in parentheses "(10.54)",
anything inside `code`. Run after StatementDeps.lean (which writes the .tsv).
"""
import re
import subprocess
import sys

FINDINGS = "FINDINGS.md"
TSV = ".lake/records_numbers.tsv"

NUM = r"[−-]?\d+(?:\.\d+)?"
TAG = r"\[(✓[A-Za-z0-9_]+|src|in|unc)\]"


def norm(s):
    return s.replace("−", "-")


def certified_pairs(text):
    m = re.search(r"^## Verified findings\n(.*?)(?=^## )", text, re.S | re.M)
    sec = m.group(1) if m else ""
    sec = re.sub(r"`[^`]*`", "", sec)
    out = {}
    for t in re.finditer(r"(" + NUM + r")\[✓([A-Za-z0-9_]+)\]", sec):
        k = (norm(t.group(1)), t.group(2))
        out[k] = out.get(k, 0) + 1
    return out


def base_check(base):
    old = subprocess.run(["git", "show", f"{base}:{FINDINGS}"], capture_output=True, text=True)
    if old.returncode != 0:
        print(f"certified-number diff: no {FINDINGS} at {base}; skipped")
        return 0
    before = certified_pairs(old.stdout)
    after = certified_pairs(open(FINDINGS, encoding="utf-8").read())
    lost = [k for k, c in before.items() if after.get(k, 0) < c]
    led = subprocess.run(["git", "diff", base, "HEAD", "--", "LEDGER.md"], capture_output=True, text=True).stdout
    added = "\n".join(l[1:] for l in led.splitlines() if l.startswith("+") and not l.startswith("+++"))
    missing = [k for k in lost if not re.search(r"(?<![\w.])" + re.escape(k[1]) + r"(?![\w])", added)]
    print(f"certified-number diff vs {base}: {len(before)} certified pairs before, {len(after)} now, "
          f"{len(lost)} removed or changed")
    for num, name in missing:
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
        cert.setdefault(name, set()).add(val)
    text = open(FINDINGS, encoding="utf-8").read()
    m = re.search(r"^## Verified findings\n(.*?)(?=^## )", text, re.S | re.M)
    if not m:
        print("::error::FINDINGS.md has no '## Verified findings' section")
        return 1
    sec = m.group(1)
    errors, counts = [], {"✓": 0, "src": 0, "in": 0, "unc": 0}
    for ln, line in enumerate(sec.split("\n")):
        s = re.sub(r"`[^`]*`", lambda mm: " " * len(mm.group()), line)
        # tagged numbers
        tagged_spans = []
        for t in re.finditer(r"(" + NUM + r")" + TAG, s):
            num, tag = norm(t.group(1)), t.group(2)
            tagged_spans.append(t.span(1))
            if tag.startswith("✓"):
                name = tag[1:]
                if name not in cert:
                    errors.append(f"[✓{name}] after {num}: no registered Checked.Records headline {name} states a RoundsTo")
                elif num not in cert[name]:
                    errors.append(f"{num}[✓{name}]: {name} certifies {sorted(cert[name])}, not {num}")
                else:
                    counts["✓"] += 1
            else:
                counts[tag] += 1
        for t in re.finditer(r"\[[^\]]*\]", s):
            body = t.group()[1:-1]
            if (body.startswith("✓") or body in ("src", "in", "unc")) and not any(
                    a <= t.start() <= b + 1 for a, b in tagged_spans):
                errors.append(f"tag [{body}] not directly after a number: {line.strip()[:80]}")
        # numbers that need a tag
        for t in re.finditer(r"(?<![\w.])(" + NUM + r")(?!\d)(?!\.\d)", s):
            a, b = t.span(1)
            num = t.group(1)
            is_dec = "." in num
            before = s[:a].rstrip()
            approx = before.endswith(("≈", "≃"))
            if not (is_dec or approx):
                continue
            if any(x == a for x, _ in tagged_spans):
                continue
            # equation numbers "(10.54)", "(11.42)–(11.45)", arXiv ids, versions
            if s[a - 1:a] == "(" and s[b:b + 1] == ")":
                continue
            if re.fullmatch(r"\d{4}\.\d{4,5}", num.lstrip("−-")):
                continue
            errors.append(f"untagged number {num}: …{s[max(0, a - 50):b + 15].strip()}…")
    total = sum(counts.values())
    print(f"certified numbers (FINDINGS.md verified findings): {counts['✓']} certified [✓], "
          f"{counts['src']} quoted [src], {counts['in']} inputs [in], {counts['unc']} unchecked [unc]; "
          f"{total} tagged")
    for e in errors:
        print(f"::error::{e}")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
