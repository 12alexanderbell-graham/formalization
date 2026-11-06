#!/usr/bin/env python3
"""Model and source names in headline prose must be backed by what the statement reaches (run 2026-11-06T0228Z,
part 3; written blind to red team M). Blocking in CI; reads .lake/meaning.jsonl.

Why: check_prose.py rule 9 asks a source named WITH A YEAR to be the source of a reached PRINTED/CLAIM
definition, and the glossary backs physics vocabulary by pinned definitions. A docstring or name could still
say "Soave", "Peng–Robinson", "SRK", "van der Waals", "printed", "Eq. (n)", "misprint" or an author's name
without a year, over a statement that reaches nothing giving that word its meaning (a Peng–Robinson docstring
over the Redlich–Kwong cubic, "Soave's κ(ω)" over coefficients nobody read, "the printed formula" over a
formula the author typed).

  python3 scripts/trust/check_source_names.py              rule on the current tree
  python3 scripts/trust/check_source_names.py --base SHA   also: baseline shrink-only, registry grows only
  python3 scripts/trust/check_source_names.py --report     print violations, never fail

Rule. For every headline (meaning.jsonl `type: headline`), its docstring and its name (camelCase and `_`
split into words) are matched against every entry of `scripts/trust/source_names.txt`
(`<key> | <python regex> | <backing> [|| <backing> ...]`; alternatives `||`, all parts of one alternative `+`).
A match must be backed by one alternative, each part of which holds:
  fixed:<def>.<param>=<lit>   the statement passes the literal <lit> to <def>'s parameter <param>
                              (meaning.jsonl `fixed`): model identity, e.g. Peng–Robinson ⇔ cubicP u = 2, w = −1;
  reach:<short name>          the statement reaches that definition (meaning.jsonl `defs` or `pinned`);
  kind:<KIND>                 the statement reaches a definition labelled KIND (PRINTED, CLAIM);
  source                      the matched text names a source of the statement: a reached PRINTED or CLAIM
                              definition whose name or docstring contains the matched text (case-insensitive,
                              dashes normalised), or a literal reading registered for this headline in
                              `scripts/trust/literal_readings.txt` with `source=<that name>` (check_literals.py
                              requires that name in the reader's brief);
  reading                     a literal reading is registered for this headline (literal_readings.txt).
Existing unbacked matches are grandfathered in the shrink-only `scripts/trust/source_names_baseline.txt`
(`<headline> <key>`), populated from the tree at run 2026-11-06T0228Z. With --base the baseline may not grow,
and the registry may not lose or change a line (a weakened entry weakens the check); added entries pass.

Limits: only headline docstrings and names are read (docstrings of definitions and module docs are frozen
and checked by check_prose rules 1/7); a name absent from the registry is not read (a new model or author
needs a registry line — add it with the first headline that uses it); the backing shows that the statement
REACHES something carrying the name, not that the source says what the docstring says.
"""
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_provenance as P  # noqa: E402
import check_literals as L  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]
REG = "scripts/trust/source_names.txt"
BASELINE = "scripts/trust/source_names_baseline.txt"
DASH = str.maketrans({"–": "-", "—": "-", "‐": "-", "‑": "-"})


def norm(s):
    return s.translate(DASH).lower()


def name_words(full):
    last = full.split(".")[-1]
    w = re.sub(r"([a-z0-9])([A-Z])", r"\1 \2", last).replace("_", " ")
    return w


def load_reg(errors):
    out = []
    for l in L.entries(REG) or []:
        ps = [x.strip() for x in l.split(" | ")]
        if len(ps) != 3:
            errors.append(f"{REG}: malformed line {l[:80]}")
            continue
        try:
            rx = re.compile(ps[1])
        except re.error as e:
            errors.append(f"{REG}: bad regex for {ps[0]}: {e}")
            continue
        alts = [[q.strip() for q in a.split("+") if q.strip()] for a in ps[2].split("||")]
        out.append((ps[0], rx, alts))
    return out


def backed(part, matched, row, defs_rows, readings):
    fixed = {(f["def"], f["param"], f["lit"]) for f in row.get("fixed", [])}
    reached = dict(row.get("defs", {}))
    for p in row.get("pinned", []):
        reached.setdefault(p, "PINNED")
    if part.startswith("fixed:"):
        m = re.fullmatch(r"fixed:([^.]+)\.([^=]+)=(.+)", part)
        return bool(m) and (m.group(1), m.group(2), m.group(3)) in fixed
    if part.startswith("reach:"):
        s = part[len("reach:"):]
        return any(d == s or d.endswith("." + s) for d in reached)
    if part.startswith("kind:"):
        return part[len("kind:"):] in reached.values()
    if part == "reading":
        return bool(readings.get(row["name"]))
    if part == "source":
        key = norm(matched)
        for d, k in reached.items():
            if k in ("PRINTED", "CLAIM"):
                dr = defs_rows.get(d, {})
                if key in norm(d) or key in norm(dr.get("doc", "")):
                    return True
        for _, srcs in readings.get(row["name"], []):
            if any(norm(s) == key or key in norm(s) for s in srcs):
                return True
        return False
    return False


def violations(rows, reg, readings):
    defs_rows = {r["name"]: r for r in rows if r.get("type") == "def"}
    out = []
    for row in rows:
        if row.get("type") != "headline":
            continue
        texts = [row.get("doc", ""), name_words(row["name"])]
        for key, rx, alts in reg:
            hits = [m.group(0) for t in texts for m in rx.finditer(t)]
            if not hits:
                continue
            for h in sorted(set(hits)):
                if not any(all(backed(p, h, row, defs_rows, readings) for p in alt) for alt in alts):
                    out.append((row["name"], key, h))
                    break
    return out


def main():
    base = sys.argv[sys.argv.index("--base") + 1] if "--base" in sys.argv else None
    report = "--report" in sys.argv
    rows = L.load_rows()
    if rows is None:
        print("check_source_names: .lake/meaning.jsonl missing (run StatementDeps.lean first)")
        return 0 if report else 1
    heads = {r["name"] for r in rows if r.get("type") == "headline"}
    errors = []
    reg = load_reg(errors)
    readings = L.load_readings(heads, [])
    bl = set()
    for l in L.entries(BASELINE) or []:
        ps = l.split()
        if len(ps) >= 2:
            bl.add((ps[0], ps[1]))
    viol = violations(rows, reg, readings)
    seen = set()
    for h, key, hit in viol:
        seen.add((h, key))
        if report:
            print(f"{h} {key}  # '{hit}'")
        elif (h, key) not in bl:
            errors.append(f"{h}: '{hit}' ({key}) in its docstring or name is not backed by what the statement "
                          f"reaches (needs one of the backings of {REG} line {key})")
    for b in sorted(bl - seen):
        errors.append(f"{BASELINE}: {b[0]} {b[1]} is backed now (or gone); remove the line (shrink-only)")
    if base:
        old = P.git("show", f"{base}:{BASELINE}")
        if old is not None:
            ob = {tuple(l.split("#")[0].split()[:2]) for l in old.splitlines() if l.split("#")[0].strip()}
            for b in sorted(bl - ob):
                errors.append(f"{BASELINE} grew against {base}: {b} (it may only shrink)")
        oldr = P.git("show", f"{base}:{REG}")
        if oldr is not None:
            now = set(L.entries(REG) or [])
            for l in oldr.splitlines():
                l = l.split("#")[0].rstrip() if not l.startswith("#") else ""
                if l.strip() and l not in now:
                    errors.append(f"{REG}: line removed or changed against {base}: {l[:80]} (the registry may only grow)")
    if report:
        print(f"check_source_names: {len(viol)} unbacked (report only)")
        return 0
    for e in errors:
        print(e)
    print(f"check_source_names: {len(reg)} names, {len(viol)} unbacked matches ({len(bl)} baselined); "
          f"{'FAIL' if errors else 'ok'}")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
