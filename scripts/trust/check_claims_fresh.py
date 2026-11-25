#!/usr/bin/env python3
"""The committed claims pages agree with the registries they print (run 2026-11-25T0628Z, annex LIV). Pure Python,
seconds; blocking in CI's trust step (BEFORE Claims.lean regenerates the pages, so it judges the committed copy) and
therefore in `records_check.py`; also run by `check_commit_msg.py --final`.

Why: CI regenerates CLAIMS.md with Lean and fails when the committed copy differs, but a run only learns that after a
push and a ~20-minute judge. Three runs in a row edited a registry that Claims.lean prints AFTER their last Claims run:
run 2026-11-20T1628Z (a literal reading registered after Claims), run 2026-11-25T0428Z (a closed reader constant
dropped from `literal_readings.txt` after Claims; CLAIMS.md stale by one line, the checked job of 45556391704 red, the
PROVED reading of a promotion delayed a run). `records_check.py` passed both times: no Python check compared the
page with the registry. This one does, for every part of a Status line that comes from a registry file alone:

  F1  the headlines of CLAIMS.md and CLAIMS_READER.md are exactly those of `scripts/trust/headlines.txt`, in order;
  F2  per headline, the reader constants printed at the head of the Status line are exactly the reader tokens of its
      `scripts/trust/literal_readings.txt` lines (first occurrence order, `source=` tokens excluded), and the count
      "N definitions written by a blind second reader" equals their number;
  F3  per headline, the grandfathered-literal count equals the literal count of its `literal_baseline.txt` line;
  F4  per headline, the number of open objections printed equals its lines in `scripts/trust/objections.txt`
      (and, since run 2026-11-25T2028Z, the number of closed ones its lines with a `closed by` field);
  F5  every Status line of CLAIMS_READER.md equals the Status line of the same headline in CLAIMS.md (one generation).

It does not replace CI's regeneration (statements, axioms, hypothesis tallies come from Lean and are checked only
there). Usage: python3 scripts/trust/check_claims_fresh.py [--selftest]
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
REG = ROOT / "scripts/trust"


def lines(p):
    out = []
    for l in Path(p).read_text(encoding="utf-8").split("\n"):
        l = l.strip()
        if l and not l.startswith("#"):
            out.append(l)
    return out


def resolve(full_names, h):
    """Claims.lean's `resolve`: a registry name is a full name or a dot-suffix of exactly one headline."""
    hits = [n for n in full_names if n == h or n.endswith("." + h)]
    return hits[0] if len(hits) == 1 else None


def parse_page(text):
    """[(full name, status line)] in page order."""
    out, cur = [], None
    for l in text.split("\n"):
        m = re.match(r"^Full name `([^`]+)`\.", l)
        if m:
            cur = m.group(1)
        elif l.startswith("**Status (generated):**") and cur is not None:
            out.append((cur, l))
            cur = None
    return out


HEAD_RE = re.compile(r"^\*\*Status \(generated\):\*\* \*\*The source's own form[^*]*\*\* (.*?)\. the statement is proved")


def printed_readers(status):
    m = HEAD_RE.match(status)
    if not m:
        return []
    names = []
    for part in m.group(1).split("; `"):
        part = part.lstrip("`")
        names.append(part.split("`", 1)[0])
    return names


def check(claims, reader, heads, readings, baseline, objections):
    errs = []
    page = parse_page(claims)
    rpage = parse_page(reader)
    names = [n for n, _ in page]
    # F1
    reg = [resolve(names, h) or h for h in heads]
    if names != reg:
        missing = [h for h in reg if h not in names]
        extra = [n for n in names if n not in reg]
        errs.append(f"F1 CLAIMS.md headlines differ from headlines.txt (missing {missing[:5]}, extra {extra[:5]}, "
                    f"or order): regenerate with `lake env lean scripts/trust/Claims.lean`")
    if [n for n, _ in rpage] != names:
        errs.append("F1 CLAIMS_READER.md headlines differ from CLAIMS.md: regenerate both with Claims.lean")
    # registries per headline
    rd, base, obj, closed = {}, {}, {}, {}
    for l in readings:
        toks = l.split()
        hn = resolve(names, toks[0])
        if hn is None:
            continue  # unresolvable lines are Claims.lean's own error
        for t in toks[1:]:
            if t.startswith("source="):
                continue
            rd.setdefault(hn, [])
            if t not in rd[hn]:
                rd[hn].append(t)
    for l in baseline:
        parts = l.split(" | ")
        if len(parts) >= 2 and not parts[0].startswith("hidden:"):
            hn = resolve(names, parts[0].strip())
            if hn:
                base[hn] = len(parts[1].split())
    for l in objections:
        parts = [p.strip() for p in l.split(" | ")]
        if len(parts) == 4:
            hn = resolve(names, parts[0])
            if hn:
                obj[hn] = obj.get(hn, 0) + 1
        elif len(parts) == 5:
            hn = resolve(names, parts[0])
            if hn:
                closed[hn] = closed.get(hn, 0) + 1
    for hn, st in page:
        want = rd.get(hn, [])
        got = printed_readers(st)
        short = lambda xs: [x.rsplit(".", 1)[-1] for x in xs]
        if [x for x in got] != want and short(got) != short(want):
            errs.append(f"F2 {hn}: CLAIMS.md prints reader constants {short(got)}, literal_readings.txt registers "
                        f"{short(want)}: a registry changed after the last Claims.lean run")
        m = re.search(r"statement literals: (\d+) definitions written by a blind second reader", st)
        n = int(m.group(1)) if m else 0
        if n != len(want):
            errs.append(f"F2 {hn}: CLAIMS.md counts {n} registered readings, literal_readings.txt has {len(want)}")
        m = re.search(r"; (\d+) literals of the statement are grandfathered", st)
        nb = int(m.group(1)) if m else None
        if nb != base.get(hn):
            errs.append(f"F3 {hn}: CLAIMS.md grandfathers {nb} literals, literal_baseline.txt {base.get(hn)}")
        m = re.search(r"OPEN FIDELITY OBJECTIONS on record \([^)]*\): (\d+):", st)
        no = int(m.group(1)) if m else 0
        if no != obj.get(hn, 0):
            errs.append(f"F4 {hn}: CLAIMS.md prints {no} open objections, objections.txt has {obj.get(hn, 0)}")
        # run 2026-11-25T2028Z (test AZ): closed entries (fifth field `closed by`) are counted the same way
        m = re.search(r"fidelity objections closed on record \([^)]*\): (\d+):", st)
        nc = int(m.group(1)) if m else 0
        if nc != closed.get(hn, 0):
            errs.append(f"F4 {hn}: CLAIMS.md prints {nc} closed objections, objections.txt has {closed.get(hn, 0)}")
    rmap = dict(rpage)
    for hn, st in page:
        if hn in rmap and rmap[hn] != st:
            errs.append(f"F5 {hn}: its Status line differs between CLAIMS.md and CLAIMS_READER.md")
    return errs


def run_tree():
    return check((ROOT / "CLAIMS.md").read_text(encoding="utf-8"),
                 (ROOT / "CLAIMS_READER.md").read_text(encoding="utf-8"),
                 lines(REG / "headlines.txt"), lines(REG / "literal_readings.txt"),
                 lines(REG / "literal_baseline.txt"), lines(REG / "objections.txt"))


def selftest():
    """Planted controls on the real tree: each mutation of a registry or a page must be caught; the tree must pass."""
    c = (ROOT / "CLAIMS.md").read_text(encoding="utf-8")
    r = (ROOT / "CLAIMS_READER.md").read_text(encoding="utf-8")
    H, L = lines(REG / "headlines.txt"), lines(REG / "literal_readings.txt")
    B, O = lines(REG / "literal_baseline.txt"), lines(REG / "objections.txt")
    fails = 0
    base = check(c, r, H, L, B, O)
    if base:
        print("selftest: the tree itself fails:", base[:3])
        fails += 1
    # the run-0428Z case: a reader token added to (or dropped from) a registration after Claims
    i = next(k for k, l in enumerate(L) if "gelfand_turning_ratio" in l)
    controls = {
        "reading added after Claims": (c, r, H, L[:i] + [L[i] + " Checked.Trust.SecondReading.gelfandSingularLambda"] + L[i + 1:], B, O),
        "reading dropped after Claims": (c, r, H, L[:i] + [" ".join(L[i].split()[:-1])] + L[i + 1:], B, O),
        "headline added to the registry": (c, r, H + ["Checked.Foo.bar"], L, B, O),
        "objection added": (c, r, H, L, B, O + ["gelfand_turning_ratio | 2026-11-25T0628Z | README.md | x"]),
        "closed objection added": (c, r, H, L, B, O + ["gelfand_turning_ratio | 2026-11-25T0628Z | README.md | x | closed by T.t"]),
        "baseline line added": (c, r, H, L, B + ["Checked.Math.GelfandTurningRatio.gelfand_turning_ratio | 7 | x"], O),
        "reader page from another generation": (c, r.replace("statement literals: 14 definitions", "statement literals: 15 definitions", 1), H, L, B, O),
    }
    for name, args in controls.items():
        if not check(*args):
            print(f"selftest: control not caught: {name}")
            fails += 1
    print(f"check_claims_fresh selftest: {len(controls)} controls, {fails} failing")
    return fails


def main(argv):
    if "--selftest" in argv:
        return 1 if selftest() else 0
    errs = run_tree()
    for e in errs:
        print("::error::" + e if "--gh" in argv else e)
    n = len(parse_page((ROOT / "CLAIMS.md").read_text(encoding="utf-8")))
    print(f"check_claims_fresh: {n} headlines; {len(errs)} problems (pages vs headlines, literal_readings, "
          f"literal_baseline, objections)")
    return 1 if errs else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
