#!/usr/bin/env python3
"""Phrases of pinned definitions in generated claims (trust track T2c/T5, run 2026-11-04T2228Z).

`CLAIMS.md` is generated from the Lean statements by `scripts/trust/Claims.lean`; the only
hand-written words in it are the phrases of pinned definitions (`scripts/trust/phrases.txt`).
This script guards them:

  check_claims.py            lint: a phrase may use a glossary term (scripts/trust/glossary.txt)
                             only if the glossary attributes that term to the phrase's own
                             definition or to a pinned definition it rests on
                             (reads .lake/phrases.jsonl written by Claims.lean)
                             P1 (run 2026-11-08T1828Z): a phrase contains no formula (no operator or
                             relation character, no hyphen-minus except between letters): Claims.lean
                             prints each pinned definition's body from Lean right after its phrase, so
                             every formula in a generated claim is printed by Lean, never by the author
                             U1: no two pinned definitions share a phrase
                             U2 (run 2026-11-08T1828Z): the first glossary term of a phrase is attributed
                             by the glossary to the phrase's own definition
                             P2 (same run, after blind red team Y, not blind): every word and number of
                             a phrase occurs in its pinning specification's text (or that of a pinned
                             definition it rests on) or is a function word: a phrase quotes the blind spec
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


FORMULA_CHARS = set("=+/·*√′″^²³⁴⁵⁽⁾ⁿ<>≤≥−×")


def formula_in_phrase(phr):
    """P1 (run 2026-11-08T1828Z, after blind round W d04): a phrase is the only hand-written text inside a generated
    claim; a formula written in it (W d04: "the Hubble rate a′(t)/a(t)" on `|hubble|`) is an author transcription of the
    body that no check compares with Lean. Claims.lean now prints the body itself next to the phrase, so phrases carry
    no formula at all: no operator or relation character, no hyphen-minus except inside a word."""
    bad = []
    for d, p in sorted(phr.items()):
        q = re.sub(r"\{[^}]*\}", "x", p)
        chars = sorted({c for c in q if c in FORMULA_CHARS})
        hy = [m.start() for m in re.finditer("-", q)
              if not (m.start() > 0 and q[m.start() - 1].isalpha() and m.start() + 1 < len(q) and q[m.start() + 1].isalpha())]
        if chars or hy:
            what = ", ".join([f"'{c}'" for c in chars] + (["a hyphen-minus outside a word"] if hy else []))
            bad.append(f"{d}: phrase contains formula characters ({what}) (P1: formulas are printed by Lean from the "
                       f"definition's body, not written in the phrase)")
    return bad


def head_noun(entries, rules):
    """U2 (run 2026-11-08T1828Z, after blind round W d04): the first glossary term of a phrase names what the definition
    is; it must be attributed by the glossary to the definition itself. `expansionRate := |hubble|` with the phrase
    "the Hubble rate ..." used a term of a definition it rests on (allowed by the attribution lint) as its own name.
    `entries`: dicts with `name`, `short`, `phrase`."""
    bad = []
    for e in entries:
        first = None
        for rx, names in rules:
            m = rx.search(e["phrase"])
            if m and (first is None or m.start() < first[0].start()):
                first = (m, names)
        if first and e["short"] not in first[1]:
            bad.append(f"{e['name']}: the first glossary term '{first[0].group(0)}' is attributed to {sorted(first[1])}, "
                       f"not to {e['short']} (U2: a phrase names its own definition first)")
    return bad


sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_claim_vocab import FUNCTION, WORD, norm, forms  # noqa: E402

NUM = re.compile(r"\d+(?:\.\d+)?")


P2_BASE = "scripts/trust/phrase_vocab_baseline.txt"


def p2_baseline(text=None):
    """(definition short name, word or number) pairs grandfathered for P2 when it was introduced (run 2026-11-08T1828Z):
    words of the formula-free phrases that the thin docstrings of their specifications do not contain (argument roles
    such as "curvature constant", units, citations). Shrink-only (`--base`): a blind writer adding them to the spec's
    docstrings, or a rewording, removes a line; nothing may be added."""
    if text is None:
        try:
            text = (ROOT / P2_BASE).read_text(encoding="utf-8")
        except FileNotFoundError:
            return set()
    out = set()
    for l in text.splitlines():
        l = l.split("#")[0].strip()
        if l:
            d, w = l.split()
            out.add((d, w))
    return out


def spec_vocabulary(entries, base=frozenset()):
    """P2 (run 2026-11-08T1828Z, after blind red team Y: not blind): a phrase may use only words and numbers that occur
    in the text of its own pinning specification or in that of a pinned definition it rests on (docstrings and field
    names of the SPEC structure or blind formulation the pin theorem uses, exported by Claims.lean as `spec_text`; the
    specs were written by blind spec writers), plus the function words of check_claim_vocab.py. Y put "conformal"
    on `hubble`, "fitted value 0.3, as verified" on `IsFlatLCDM`, "no claim is made there" on `decel` and swapped
    equation numbers between `FriedmannEq` and `MasterEq`: words and numbers no check read. A quotation rule, not a
    deny-list (PROMPT working notes 145, 164)."""
    by_short = {e["short"]: e for e in entries}
    bad = []
    for e in entries:
        text = " ".join([e.get("spec_text", "")] + [by_short[r].get("spec_text", "") for r in e.get("rests_on", [])
                                                    if r in by_short])
        allowed = {norm(w) for w in WORD.findall(text)}
        nums = set(NUM.findall(text))
        ph = re.sub(r"\{[^}]*\}", " ", e["phrase"])
        extra = {w for (s, w) in base if s == e["short"]}
        miss = sorted({norm(w) for w in WORD.findall(ph) if not (forms(norm(w)) & (allowed | FUNCTION | extra))})
        miss += sorted({n for n in NUM.findall(ph) if n not in nums and n not in extra})
        if miss:
            bad.append(f"{e['name']}: phrase words not in its pinning specification's text or in a function word list: "
                       f"{miss} (P2: a phrase quotes the blind spec)")
    return bad


def _controls():
    ok = not duplicate_phrases({"A.f": "the rate of {a} at {t}", "A.g": "the size of {a}"})
    bad = duplicate_phrases({"A.f": "the rate of {a} at {t}", "A.g": "The rate of {b} at {s}"})
    if not ok or len(bad) != 1:
        print("::error::check_claims U1 controls failed")
        return 1
    ok = not formula_in_phrase({"A.f": "the angular-diameter distance of {a} at time {t₀} (Eq. (11.6))"})
    bad = formula_in_phrase({"A.f": "the rate a′({t})/a({t}) of {a}"})
    bad2 = formula_in_phrase({"A.f": "the rate of {a} minus -1"})
    if not ok or len(bad) != 1 or len(bad2) != 1:
        print("::error::check_claims P1 controls failed")
        return 1
    gl = [(re.compile(r"(?i)hubble (rate|parameter|function)"), {"hubble", "IsFlatLCDM"}),
          (re.compile(r"(?i)\bredshift"), {"redshift"})]
    ok = not head_noun([{"name": "A.hubble", "short": "hubble", "phrase": "the Hubble rate of {a}"},
                        {"name": "A.IsFlatLCDM", "short": "IsFlatLCDM", "phrase": "{a} obeys a law with a Hubble rate and a redshift"},
                        {"name": "A.g", "short": "g", "phrase": "the size of {a}"}], gl)
    bad = head_noun([{"name": "A.expansionRate", "short": "expansionRate", "phrase": "the Hubble rate of {a}"},
                     {"name": "A.h", "short": "hubble", "phrase": "the rate of {a} at the redshift of {t}, a Hubble rate"}], gl)
    if not ok or len(bad) != 2:
        print("::error::check_claims U2 controls failed")
        return 1
    sp = [{"name": "A.hubble", "short": "hubble", "rests_on": [], "spec_text": "Specification of the Hubble rate of a scale factor at time t, Eq. (11.6)",
           "phrase": "the Hubble rate of the scale factor {a} at time {t} (Eq. (11.6))"}]
    ok = not spec_vocabulary(sp)
    bad = spec_vocabulary([dict(sp[0], phrase="the conformal Hubble rate of the scale factor {a} at time {t} (Eq. (11.5))")])
    if not ok or len(bad) != 1 or "conformal" not in bad[0] or "11.5" not in bad[0]:
        print("::error::check_claims P2 controls failed")
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
    entries = []
    for line in data.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        e = json.loads(line)
        entries.append(e)
        n += 1
        allowed = {e["short"], *e["rests_on"]}
        for rx, names in rules:
            m = rx.search(e["phrase"])
            if m and not (names & allowed):
                bad.append(f"{e['name']}: phrase uses '{m.group(0)}' (glossary: {sorted(names)}), "
                           f"but the definition is {e['short']} and rests on {sorted(e['rests_on'])}")
    phr = parse_phrases((ROOT / PHR).read_text(encoding="utf-8"))
    bad += duplicate_phrases(phr)
    bad += formula_in_phrase(phr)
    bad += head_noun(entries, rules)
    bad += spec_vocabulary(entries, p2_baseline())
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
    ob = git("show", f"{base}:{P2_BASE}")
    if ob.returncode == 0:
        added = sorted(p2_baseline() - p2_baseline(ob.stdout))
        if added:
            for d, w in added:
                print(f"P2 baseline line added since {base}: {d} {w} (shrink-only)")
            return 1
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
