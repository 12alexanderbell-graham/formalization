#!/usr/bin/env python3
"""Headline prose may not add a claim the statement does not make (run 2026-11-06T1428Z, part 3; written AFTER
reading blind red team O's report — not blind). Blocking in CI; reads .lake/meaning.jsonl.

Why: rounds F, G, J, N and O each put the false part of a claim into words of a true headline that no rule read.
Round O (6 defects against the round-N scripts, 6/6 forecast accepted): d01 a one-sided bound described as
"reproduced to within 10⁻⁹"; d04 "…, so B stays below 10⁻⁵ during the run" over a bound at t = 40 only;
d05 "…, so it is safe to use … and gives a usable attraction parameter"; d06 generality carried by the
headline's NAME (`rob_c_stays_below_29_percent_at_all_times`). Two of these are structural, not vocabulary:
a docstring that draws a consequence ("so", "hence", "therefore") states something beyond the statement by
construction, and a name is reader-facing prose like the docstring.

  python3 scripts/trust/check_claim_words.py              rules W1-W5 on the current tree
  python3 scripts/trust/check_claim_words.py --base SHA   also W6 (baseline shrink-only)
  python3 scripts/trust/check_claim_words.py --report     print every finding, never fail

W1 (inference): a headline docstring contains no inference connective — so (not "so-called", "and so on",
   "so far"), hence, therefore, thus, consequently, which means, it follows, this means, this shows,
   showing that, implying. A docstring says what the statement proves; what follows from it is a further
   claim that needs its own headline.
W2 (name generality): the headline's name after `Checked.<Area>.` (namespaces too, since run 2026-11-06T2228Z), read as words (`_` → space), is checked with
   check_prose_gen's words (DOMAIN: always, at all times, throughout, everywhere, …; CASES: globally, in
   general, …) plus stays/remains/forever/global/uniform/any/every/all: a DOMAIN or stays-word needs a
   universally bound non-function variable in the statement (a time, a point, a parameter); a CASES word or
   any/every/all needs universally bound data at all.
W3 (two-sided words): "to within", "within … of", "reproduce(s/d)", "agree(s) with", "match(es)", "confirm(s/ed)"
   in a docstring need a two-sided conclusion: an absolute value `|…|`, or at least two comparisons
   (`<`, `≤`, `>`, `≥`) in the conclusion. A one-sided bound reproduces nothing to within anything.
W4 (persistence over time): stays, remains, keeps, during, persists in a docstring need a universally bound
   non-function variable (as check_prose_gen G1 for its DOMAIN words; "stays below … during the run" over
   `y₂ 40` fails).
W5 (grading, extends check_prose_eval E1): safe, safely, usable, usability, can be used, works well,
   suitable, fit for purpose, dependable, sound (as a grade), valid for/over/on, applicable.
W6 (--base): `scripts/trust/claim_words_baseline.txt` (keys `<headline>|<rule>|<word>`, populated from the
   tree when the rule was written) may only shrink.

Limits: inference without a listed connective ("…; B is small"), generality or grades in words not listed,
names in other conventions (camelCase words are split too, but abbreviations are not read), and prose outside
headline docstrings and names (Work modules, STATE.md, run records) are not read here.
"""
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_prose as C  # noqa: E402
import check_prose_gen as G  # noqa: E402
import check_literals as L  # noqa: E402
import check_provenance as P  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]
BASELINE = "scripts/trust/claim_words_baseline.txt"

INFER = re.compile(r"(?i)\b(?:so(?![-‑]called)(?!\s+on\b)(?!\s+far\b)|hence|therefore|thus|consequently|"
                   r"which\s+means|it\s+follows|this\s+means|this\s+shows|showing\s+that|implying)\b")
NAME_EXTRA_DOMAIN = re.compile(r"(?i)\b(?:stays?|remains?|forever|global|uniform|uniformly)\b")
NAME_EXTRA_CASES = re.compile(r"(?i)\b(?:any|every|all)\b")
TWO_SIDED = re.compile(r"(?i)\bto\s+within\b|\bwithin\s+\S+(?:\s+\S+)?\s+of\b|\breproduc(?:e|es|ed|ing)\b|"
                       r"\bagrees?\s+with\b|\bmatch(?:es|ed)?\b|\bconfirm(?:s|ed)?\b")
PERSIST = re.compile(r"(?i)\b(?:stays?|remains?|keeps?|during|persists?)\b")
GRADE = re.compile(r"(?i)\bsafe(?:ly)?\b|\busab(?:le|ility)\b|\bcan\s+be\s+used\b|\bworks?\s+well\b|\bsuitab(?:le|ility)\b|"
                   r"\bfit\s+for\s+purpose\b|\bdependab\w*|\bsound\b|\bvalid\s+(?:for|over|on)\b|\bapplicab\w*")


def name_words(name):
    # every component after `Checked.<Area>.` is read (run 2026-11-06T2228Z, blind red team P d03: generality
    # carried by a namespace, `Checked.Sim.RobertsonAllTimes.rob_exists_1e11`, whose heading in CLAIMS.md is
    # `RobertsonAllTimes.rob_exists_1e11`; W2 read only the last component)
    parts = name.split(".")
    parts = parts[2:] if len(parts) > 2 and parts[0] in ("Checked", "Work") else parts[-1:]
    last = " ".join(parts)
    last = re.sub(r"([a-z])([A-Z])", r"\1 \2", last)
    return " ".join(w for w in re.split(r"[_\s]+", last) if w)


def conclusion(row):
    s = L.statement_text(row.get("module", ""), row["name"])
    if s is None:
        return None
    toks = L.lex(s)
    i = 0
    while i < len(toks) and toks[i] in L.OPEN:
        i = L.group_end(toks, i)
    if i < len(toks) and toks[i] == ":":
        i += 1
    return toks[i:]


def findings(h):
    out = []
    doc = C.strip_citations(C.strip_code_names(h.get("doc", "") or ""))
    name = h["name"]
    scal = G.scalar_bound(h)
    univ = bool(h.get("universal"))
    for m in INFER.finditer(doc):
        out.append((f"{name}|W1|{' '.join(m.group(0).lower().split())}",
                    f"W1: {name}: its docstring draws a consequence ('{m.group(0)}'): say what the statement proves; "
                    f"a consequence is a further claim that needs its own headline"))
        break
    nw = name_words(name)
    for m in list(G.WORDS.finditer(nw)) + list(NAME_EXTRA_DOMAIN.finditer(nw)) + list(NAME_EXTRA_CASES.finditer(nw)):
        w = " ".join(m.group(0).lower().split())
        domain = bool(G.DOMAIN_RX.match(m.group(0))) or bool(NAME_EXTRA_DOMAIN.fullmatch(m.group(0)))
        if (domain and not scal) or (not domain and not univ):
            out.append((f"{name}|W2|{w}", f"W2: {name}: its name says '{m.group(0)}', but the statement "
                        f"{'binds no time, point or parameter' if domain else 'binds no universally quantified data'} "
                        f"(bound: {h.get('bound') or 'nothing'}): the name generalises beyond what is proved"))
            break
    m = TWO_SIDED.search(doc)
    if m:
        concl = conclusion(h)
        ncmp = sum(t in ("<", "≤", ">", "≥") for t in concl) if concl is not None else 0
        if concl is None or ("|" not in concl and ncmp < 2):
            if True:
                out.append((f"{name}|W3|{' '.join(m.group(0).lower().split()[:2])}",
                            f"W3: {name}: its docstring says '{m.group(0)}' (agreement within a tolerance), but the "
                            f"conclusion is one-sided ({ncmp} comparison, no absolute value)"))
    if not scal:
        m = PERSIST.search(doc)
        if m:
            out.append((f"{name}|W4|{m.group(0).lower()}",
                        f"W4: {name}: its docstring says '{m.group(0)}' (persistence over time), but the statement "
                        f"binds no time, point or parameter (bound: {h.get('bound') or 'nothing'})"))
    m = GRADE.search(doc)
    if m:
        out.append((f"{name}|W5|{' '.join(m.group(0).lower().split())}",
                    f"W5: {name}: its docstring grades ('{m.group(0)}'); no statement certifies that a model or "
                    f"correlation is safe, usable or valid: say what the statement proves"))
    return out


def main():
    base = sys.argv[sys.argv.index("--base") + 1] if "--base" in sys.argv else None
    report = "--report" in sys.argv
    mp = ROOT / ".lake/meaning.jsonl"
    if not mp.exists():
        print("check_claim_words: .lake/meaning.jsonl missing (run StatementDeps.lean first)")
        return 0 if report else 1
    C.load_nouns()
    rows = [json.loads(l) for l in mp.read_text().splitlines() if l.strip()]
    C.KNOWN.update(C.short(r["name"]) for r in rows)
    C.KNOWN.update(r["name"] for r in rows)
    found = []
    for h in (r for r in rows if r["type"] == "headline"):
        found += findings(h)
    keys = {k for k, _ in found}
    bp = ROOT / BASELINE
    bl = {l.split("#")[0].strip() for l in bp.read_text().splitlines() if l.split("#")[0].strip()} if bp.exists() else set()
    if report:
        for k, m in found:
            print(f"{k}\n    {m}")
        print(f"check_claim_words: {len(found)} findings (report only)")
        return 0
    errors = [m for k, m in found if k not in bl]
    errors += [f"{BASELINE}: {k} no longer fires; remove the line (shrink-only)" for k in sorted(bl - keys)]
    if base:
        old = P.git("show", f"{base}:{BASELINE}")
        if old is not None:
            ob = {l.split("#")[0].strip() for l in old.splitlines() if l.split("#")[0].strip()}
            errors += [f"{BASELINE} grew against {base}: {k} (it may only shrink)" for k in sorted(bl - ob)]
        # a baseline absent at the base is the commit introducing the rule (populated from that tree)
    for e in errors:
        print("  " + e)
    print(f"check_claim_words: {sum(r['type'] == 'headline' for r in rows)} headlines, {len(found)} findings "
          f"({len(bl & keys)} baselined); {'FAIL' if errors else 'ok'}")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
