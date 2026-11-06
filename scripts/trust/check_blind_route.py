#!/usr/bin/env python3
"""Structural evidence that a reader file was written from its brief, not by the author (run 2026-11-06T0228Z,
part 3; written blind to red team M). Blocking in CI (needs --base; without it only reports what it would check).

Why: check_provenance.py rule 4 requires a second version in `Checked/Trust/` to be a copy of a file under
`runs/<run>/`, next to a brief, committed before the copy. An author can still write the "reading" himself,
commit it under runs/ with a plausible brief, and copy it (round L limit 1). Blindness itself is not
mechanically checkable; this script checks what a forged route must otherwise get wrong, for every second
version (non-generated `Checked/Trust/SecondReading*` / `SecondFormulation*` module) added or changed
against SHA:

  python3 scripts/trust/check_blind_route.py --base SHA

B1 (order): the reader file (the module's code-identical copy under runs/, as check_provenance rule 4 finds
   it) is new since SHA and has a brief (`*brief*.md`) in its own directory (since run 2026-11-06T0228Z: not a parent;
   the brief must itself be added since SHA) inside
   `runs/<run>/` that was committed in a commit strictly BEFORE the commit adding the reader file, which
   itself is strictly before the first commit since SHA touching the Checked module: brief, reading, copy —
   three commits, in this order. (A reader file that already existed at SHA passes B1-B4: it was checked
   when it was added.)
B2 (brief frozen): the brief is not modified after the commit that adds the reader file (no brief edited
   afterwards to fit the reading).
B3 (brief does not contain the answer): no decimal literal (`0.480`), fraction `a / b` with an operand of
   two or more digits, or integer of three or more digits from the reader file's code occurs in the brief
   (numbers compared by value; a brief that hands over the data is not a blind reading); and no line of
   the reader file's code of 25 or more non-space characters occurs in the brief.
B4 (isolation): the commit adding the reader file changes nothing outside `runs/<run>/`, and the commit
   adding the brief adds no `.lean` file and changes nothing under `Checked/`, `Work/` or `scripts/`.

What remains uncheckable (recorded): that the reader was a different agent, that it did not see the program
text or the source answer by another channel, and that the brief describes the source honestly. An author
who writes a brief without the answer, commits it, writes a forged reading in a separate commit touching only
runs/, and copies it in a third commit passes every rule here; LEDGER disclosure and the reader's blind
side observations (disagreements found) remain the only evidence of blindness.
"""
import re
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_provenance as P  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]


def commits_since(base):
    return (P.git("rev-list", "--reverse", f"{base}..HEAD") or "").split()


def first_commit(base, path, flt=None):
    args = ["log", "--format=%H", "--reverse"] + ([f"--diff-filter={flt}"] if flt else []) + [f"{base}..HEAD", "--", path]
    out = (P.git(*args) or "").split()
    return out[0] if out else None


def changed_files(c):
    return [l for l in (P.git("show", "--name-status", "--format=", c) or "").splitlines() if l.strip()]


def briefs_for(copy):
    """brief files in the copy's own directory (run 2026-11-06T0228Z, after judging round M d03: a brief in a
    parent folder — there the red team's own brief, committed long before — let a forged reading pass B1-B4;
    the reader's brief must sit next to the reader file, and the directory must be new since the base)"""
    parts = copy.split("/")
    d = ROOT / "/".join(parts[:-1])
    return [str(f.relative_to(ROOT)) for f in sorted(d.iterdir())
            if f.is_file() and f.suffix == ".md" and re.search(r"brief", f.name, re.I)]


NUM = re.compile(r"(?<![\w.])(\d+\.\d+|\d+)(?![\w.]|\.\d)")
FRAC = re.compile(r"(?<![\w.])(\d+)\s*/\s*(\d+)(?![\w.])")


def answer_numbers(code):
    vals = set()
    for m in re.finditer(r"(?<![\w.])\d+\.\d+(?![\w.])", code):
        vals.add(Fraction(m.group(0)))
    for m in FRAC.finditer(code):
        a, b = m.group(1), m.group(2)
        if len(a) >= 2 or len(b) >= 2:
            vals.add(Fraction(int(a), int(b)) if int(b) else None)
            vals.add(Fraction(int(a)) if len(a) >= 2 else None)
    for m in re.finditer(r"(?<![\w.])\d{3,}(?![\w.])", code):
        vals.add(Fraction(m.group(0)))
    vals.discard(None)
    return vals


def brief_numbers(text):
    vals = set()
    for m in NUM.finditer(text):
        vals.add(Fraction(m.group(1)))
    for m in FRAC.finditer(text):
        if int(m.group(2)):
            vals.add(Fraction(int(m.group(1)), int(m.group(2))))
    return vals


def check_module(rel, base, order, errors):
    code = P.code((ROOT / rel).read_text())
    copies = P.runs_copies(code)
    if not copies:
        return  # check_provenance.py rule 4 reports it
    if any(P.git("cat-file", "-e", f"{base}:{c}") is not None for c in copies):
        return
    problems = []
    for c in copies:
        added = first_commit(base, c, "A")
        touched = first_commit(base, rel)
        if not added or not touched:
            problems.append(f"{c}: not committed yet (order checked on the pushed history)")
            continue
        bs = briefs_for(c)
        if not bs:
            problems.append(f"{c}: no brief in its directory or a parent inside its run folder")
            continue
        run_root = "/".join(c.split("/")[:2]) + "/"
        p = []
        if not order.index(added) < order.index(touched):
            p.append("B1: the reader file is not committed before the Checked copy")
        good_brief = None
        for b in bs:
            badd = first_commit(base, b, "A")
            at_base = P.git("cat-file", "-e", f"{base}:{b}") is not None
            if at_base or badd is None or not order.index(badd) < order.index(added):
                continue  # the brief must be new since the base and committed strictly before the reading
            later = [x for x in (P.git("log", "--format=%H", f"{added}..HEAD", "--", b) or "").split()]
            if later:
                p.append(f"B2: brief {b} modified after the reader file was committed")
                continue
            good_brief = b
            break
        if good_brief is None:
            p.append(f"B1: no brief of {bs} committed strictly before the reader file")
        else:
            text = (ROOT / good_brief).read_text(errors="replace")
            leaked = sorted(answer_numbers(code) & brief_numbers(text))
            if leaked:
                p.append(f"B3: brief {good_brief} contains the reader's numbers {[str(x) for x in leaked][:6]}")
            flat = re.sub(r"\s+", "", text)
            for line in code.splitlines():
                ln = re.sub(r"\s+", "", line)
                if len(ln) >= 25 and ln in flat:
                    p.append(f"B3: brief {good_brief} contains the reader's code line {line.strip()[:60]!r}")
                    break
            if not P.git("cat-file", "-e", f"{base}:{good_brief}") is not None:
                for l in changed_files(first_commit(base, good_brief, "A")):
                    f = l.split("\t")[-1]
                    if f.endswith(".lean") and l.startswith("A") or f.startswith(("Checked/", "Work/", "scripts/")):
                        p.append(f"B4: the commit adding brief {good_brief} also changes {f}")
                        break
        for l in changed_files(added):
            f = l.split("\t")[-1]
            if not f.startswith(run_root):
                p.append(f"B4: the commit adding {c} also changes {f} (outside {run_root})")
                break
        if not p:
            return
        problems.append(f"{c}: " + "; ".join(p))
    errors.append(f"{rel}: no reader file passes the blind-route rules: " + " | ".join(problems))


def main():
    if "--base" not in sys.argv:
        print("check_blind_route: needs --base SHA (rules apply to second versions added or changed since SHA)")
        return 0
    base = sys.argv[sys.argv.index("--base") + 1]
    if P.git("cat-file", "-e", f"{base}^{{commit}}") is None:
        print(f"check_blind_route: base {base} not available; skipped")
        return 0
    order = commits_since(base)
    errors, n = [], 0
    for rel in P.all_lean():
        if not P.second_module(rel) or Path(rel).name in P.GENERATED:
            continue
        if P.git("show", f"{base}:{rel}") == (ROOT / rel).read_text():
            continue
        n += 1
        check_module(rel, base, order, errors)
    for e in errors:
        print(e)
    print(f"check_blind_route: {n} second versions added or changed since {base[:12]}; {'FAIL' if errors else 'ok'}")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
