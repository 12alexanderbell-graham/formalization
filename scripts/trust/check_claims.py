#!/usr/bin/env python3
"""Phrases of pinned definitions in generated claims (trust track T2c/T5, run 2026-11-04T2228Z).

`CLAIMS.md` is generated from the Lean statements by `scripts/trust/Claims.lean`; the only
hand-written words in it are the phrases of pinned definitions (`scripts/trust/phrases.txt`).
This script guards them:

  check_claims.py            lint: a phrase may use a glossary term (scripts/trust/glossary.txt)
                             only if the glossary attributes that term to the phrase's own
                             definition or to a pinned definition it rests on
                             (reads .lake/phrases.jsonl written by Claims.lean)
  check_claims.py --base B   a phrase changed or removed since commit B needs a LEDGER.md line
                             added since B naming the definition (as check_relock.py does for
                             frozen fingerprints)

Why: a wrong phrase would put false meaning into every generated claim that uses the definition
(e.g. calling `angDist` a luminosity distance), exactly the class the generated claims remove.
"""
import json, re, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PHR = "scripts/trust/phrases.txt"


def git(*args):
    return subprocess.run(["git", *args], capture_output=True, text=True, cwd=ROOT)


def parse_phrases(text):
    out = {}
    for line in text.splitlines():
        s = line.strip()
        if not s or s.startswith("#") or " | " not in s:
            continue
        d, p = s.split(" | ", 1)
        out[d.strip()] = p.strip()
    return out


def glossary():
    rules = []
    for line in (ROOT / "scripts/trust/glossary.txt").read_text(encoding="utf-8").splitlines():
        if not line.strip() or line.startswith("#") or "=>" not in line:
            continue
        rx, names = line.rsplit("=>", 1)
        rules.append((re.compile(rx.strip()), set(names.split())))
    return rules


def duplicate_phrases(phr):
    """U1 (blind red team W, run 2026-11-08T1428Z, d04): two different pinned definitions may not carry the same
    phrase (placeholders and case ignored): `expansionRate := |hubble|` was registered with the phrase of `hubble`,
    so every generated claim using it said "the Hubble rate a′(t)/a(t)" of a different function."""
    seen, bad = {}, []
    for d, p in sorted(phr.items()):
        key = re.sub(r"\{[^}]*\}", "{}", p).lower().strip()
        if key in seen:
            bad.append(f"{d}: phrase identical to that of {seen[key]} (U1: a reader of the generated claims could not "
                       f"tell the two definitions apart)")
        else:
            seen[key] = d
    return bad


def _controls():
    ok = not duplicate_phrases({"A.f": "the rate of {a} at {t}", "A.g": "the size of {a}"})
    bad = duplicate_phrases({"A.f": "the rate of {a} at {t}", "A.g": "The rate of {b} at {s}"})
    if not ok or len(bad) != 1:
        print("::error::check_claims U1 controls failed")
        return 1
    return 0


def lint():
    if _controls():
        return 1
    data = ROOT / ".lake/phrases.jsonl"
    if not data.exists():
        print(".lake/phrases.jsonl missing: run `lake env lean scripts/trust/Claims.lean` first")
        return 1
    rules = glossary()
    bad = []
    n = 0
    for line in data.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        e = json.loads(line)
        n += 1
        allowed = {e["short"], *e["rests_on"]}
        for rx, names in rules:
            m = rx.search(e["phrase"])
            if m and not (names & allowed):
                bad.append(f"{e['name']}: phrase uses '{m.group(0)}' (glossary: {sorted(names)}), "
                           f"but the definition is {e['short']} and rests on {sorted(e['rests_on'])}")
    bad += duplicate_phrases(parse_phrases((ROOT / PHR).read_text(encoding="utf-8")))
    for b in bad:
        print("PHRASE:", b)
    print(f"phrases: {n} checked, {len(bad)} problems")
    return 1 if bad else 0


def base_check(base):
    if not base or set(base) == {"0"} or git("cat-file", "-e", base + "^{commit}").returncode:
        base = "HEAD~1"
    old = git("show", f"{base}:{PHR}")
    if old.returncode:
        print(f"no {PHR} at {base}: nothing to compare")
        return 0
    old = parse_phrases(old.stdout)
    new = parse_phrases((ROOT / PHR).read_text(encoding="utf-8"))
    changed = sorted(d for d, p in old.items() if new.get(d) != p)
    if not changed:
        print(f"phrases: {len(old)} at {base}, none changed or removed")
        return 0
    diff = git("diff", base, "HEAD", "--", "LEDGER.md").stdout
    added = "\n".join(l[1:] for l in diff.splitlines() if l.startswith("+") and not l.startswith("+++"))
    missing = []
    for d in changed:
        last = re.escape(d.split(".")[-1])
        if not (d in added or re.search(r"(?<![\w'])" + last + r"(?![\w'])", added)):
            missing.append(d)
        print(("removed" if d not in new else "changed") + f" phrase: {d}" +
              ("  -- NOT named in a LEDGER.md addition" if d in missing else ""))
    return 1 if missing else 0


if __name__ == "__main__":
    if "--base" in sys.argv:
        i = sys.argv.index("--base")
        sys.exit(base_check(sys.argv[i + 1] if i + 1 < len(sys.argv) else ""))
    sys.exit(lint())
