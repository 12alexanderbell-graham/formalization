#!/usr/bin/env python3
"""More generalising words need universally bound data (run 2026-11-06T1028Z, part 3; written blind to red team N).
Blocking in CI; reads .lake/meaning.jsonl. Extends check_prose.py rules 3, 6 and 10 (that script is unchanged).

Why: check_prose.py rule 6 reads only every, any, all, each, whatever, whichever, regardless of, irrespective
of, independent(ly) of, does not depend on, no matter, arbitrary, uniform(ly), for all. A docstring can
generalise over time, space or cases with other words — "throughout", "at all times", "always", "for the
whole interval", "everywhere", "never", "uniformly in time", "forever", "globally", "in general" — over a
statement that fixes the time (`y₂ 40`), a point or a parameter, and no rule reads them.

  python3 scripts/trust/check_prose_gen.py              rules G1-G3 on the current tree
  python3 scripts/trust/check_prose_gen.py --base SHA   also G4 (baseline shrink-only)
  python3 scripts/trust/check_prose_gen.py --report     print every finding, never fail

Words (WORDS below): throughout, at all times, at all time(s)/points, all the time, always, never, forever, for
ever, for all time, at no time, everywhere, anywhere, wherever, whenever, nowhere, for the whole, over the whole,
on the whole, across the whole, along the whole, the entire, for the entire, over the entire, in general,
generally, globally, universally, invariably, without exception, unconditionally, in all cases, in every case,
uniformly in time / in t / in space, permanently, at every instant, at each instant, at any instant, for all
times, all along, from start to end, regardless, irrespective, independently, for each and every, no matter.
G1 (rule 6 with these words): check_prose.param_rule runs with these words as the generalising words. A
   phrase after one of them that names a parameter the statement FIXES to a number is reported (e.g.
   "for the whole range of amplitudes" when the amplitude is fixed). The words of time and space ("always",
   "throughout", "never", "everywhere", …) usually name no noun after them ("always positive"), so for these
   a phrase that names nothing bound passes if the statement universally binds a variable of a non-function
   type (a time, a point, a parameter: `∀ t`, a binder `(t : ℝ)`); otherwise it is reported — "y₂ stays
   positive throughout" over a statement about `y₂ 40` fails.
G2 (rule 3 with these words): a headline whose statement binds no universally quantified data at all may not
   use any of these words.
G3 (rule 10 with these words): a docstring that uses one of these words over data the statement restricts by
   a pinned model predicate (`Is…`) must contain a glossary term backed by that predicate.
Existing findings on the tree at 6fc653c are listed in the shrink-only `scripts/trust/prose_gen_baseline.txt`
(keys `<headline>|<rule>|<word ...>`, one per line, each with a reason).
G4 (--base): the baseline may not grow.

Limits: generality without any such word ("isochronous", "amplitude-independent", "the solution stays
positive"), words in other languages, generality carried by the headline's name only, and whether a bound
variable of the statement is really the one the word ranges over (a statement binding `t` for one purpose
and fixing the time elsewhere passes G1) are not read.
"""
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_prose as C  # noqa: E402
import check_provenance as P  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]
BASELINE = "scripts/trust/prose_gen_baseline.txt"
DOMAIN = (r"throughout|at\s+all\s+(?:times?|points?|instants?)|all\s+the\s+time|always|never|for\s*ever|"
          r"for\s+all\s+times?|at\s+no\s+time|everywhere|anywhere|wherever|whenever|nowhere|"
          r"(?:for|over|on|across|along)\s+the\s+(?:whole|entire)|the\s+entire|all\s+along|from\s+start\s+to\s+end|"
          r"uniformly\s+in\s+(?:time|t|space|x|z)|permanently|at\s+(?:every|each|any)\s+(?:instant|moment|time)")
CASES = (r"in\s+general|generally|globally|universally|invariably|without\s+exception|unconditionally|"
         r"in\s+all\s+cases|in\s+every\s+case|regardless|irrespective|independently|for\s+each\s+and\s+every")
WORDS = re.compile(r"(?i)\b(" + DOMAIN + "|" + CASES + r")\b")
DOMAIN_RX = re.compile(r"(?i)^(?:" + DOMAIN + r")$")


def scalar_bound(h):
    """does the statement universally bind a variable of a non-function type?"""
    for b in h.get("bound", []):
        n, _, ty = b.partition(" : ")
        if ty.strip() and "→" not in ty:
            return True
    return False


def findings(h, gloss):
    out = []
    text = C.strip_citations(C.strip_code_names(h.get("doc", "")))
    if not WORDS.search(text):
        return out
    if not h.get("universal"):
        m = WORDS.search(text)
        out.append((f"{h['name']}|G2|{m.group(0).lower()}", f"{h['name']}: the docstring says '{m.group(0)}' but the "
                    f"statement binds no universally quantified data (it is about fixed objects)"))
    if "bound" in h:
        errs = []
        saved = C.GEN
        try:
            C.GEN = WORDS
            C.param_rule(h, errs)
        finally:
            C.GEN = saved
        for k, msg in errs:
            trig = k.split("|param|", 1)[1].split()[0] if "|param|" in k else ""
            word = re.search(r"'([^']*)'", msg)
            w = word.group(1) if word else trig
            is_domain = any(DOMAIN_RX.match(" ".join(w.split()[:n])) for n in range(1, 5))
            if "binds nothing it could refer to" in msg and is_domain:
                continue  # time/space words: judged below by what the statement binds, not by the phrase
            out.append((k.replace("|param|", "|G1|"), msg + " [check_prose_gen G1]"))
        if not scalar_bound(h):
            for m in WORDS.finditer(text):
                if DOMAIN_RX.match(m.group(0)):
                    out.append((f"{h['name']}|G1|{' '.join(m.group(0).lower().split())}",
                                f"{h['name']}: its docstring says '{m.group(0)}' (over time, space or a whole range), but "
                                f"the statement universally binds no time, point or parameter (bound: "
                                f"{h.get('bound') or 'nothing'}): it is proved at fixed values only [check_prose_gen G1]"))
                    break
        bnames = {C.norm_tok(b.partition(" : ")[0]) for b in h["bound"]}
        restr = sorted({r.split(".")[0] for v, r in h.get("roles", [])
                        if C.norm_tok(v) in bnames and not r.startswith("=") and r.split(".")[0].startswith("Is")})
        for d in restr:
            terms = [c for _, c, backs in gloss if d in backs]
            if terms and not any(c.search(text) for c in terms):
                out.append((f"{h['name']}|G3|{d}", f"{h['name']}: its docstring generalises ('{WORDS.search(text).group(0)}') "
                            f"but never names the restriction `{d}` the statement puts on its data"))
    return out


def main():
    base = sys.argv[sys.argv.index("--base") + 1] if "--base" in sys.argv else None
    report = "--report" in sys.argv
    mp = ROOT / ".lake/meaning.jsonl"
    if not mp.exists():
        print("check_prose_gen: .lake/meaning.jsonl missing (run StatementDeps.lean first)")
        return 0 if report else 1
    C.load_nouns()
    rows = [json.loads(l) for l in mp.read_text().splitlines() if l.strip()]
    C.KNOWN.update(C.short(r["name"]) for r in rows)
    C.KNOWN.update(r["name"] for r in rows)
    gloss = []
    for l in (ROOT / "scripts/trust/glossary.txt").read_text().splitlines():
        if l.strip() and not l.startswith("#"):
            rx, backs = l.split(" => ")
            gloss.append((rx, re.compile(rx), set(backs.split())))
    found = []
    for h in (r for r in rows if r["type"] == "headline"):
        found += findings(h, gloss)
    keys = {k for k, _ in found}
    bp = ROOT / BASELINE
    bl = {l.split("#")[0].strip() for l in bp.read_text().splitlines() if l.split("#")[0].strip()} if bp.exists() else set()
    if report:
        for k, m in found:
            print(f"{k}\n    {m}")
        print(f"check_prose_gen: {len(found)} findings (report only)")
        return 0
    errors = [m for k, m in found if k not in bl]
    errors += [f"{BASELINE}: {k} no longer fires; remove the line (shrink-only)" for k in sorted(bl - keys)]
    if base:
        old = P.git("show", f"{base}:{BASELINE}")
        if old is not None:
            ob = {l.split("#")[0].strip() for l in old.splitlines() if l.split("#")[0].strip()}
            errors += [f"{BASELINE} grew against {base}: {k} (it may only shrink)" for k in sorted(bl - ob)]
    for e in errors:
        print("  " + e)
    print(f"check_prose_gen: {sum(r['type'] == 'headline' for r in rows)} headlines, {len(found)} findings "
          f"({len(bl & keys)} baselined); {'FAIL' if errors else 'ok'}")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
