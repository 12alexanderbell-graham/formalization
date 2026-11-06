#!/usr/bin/env python3
"""Model and source names in any spelling, each backed by evidence about THAT name for THAT headline (run
2026-11-06T1028Z, part 3; written blind to red team N). Blocking in CI; reads .lake/meaning.jsonl.

Why: check_source_names.py matches regexes that miss spelling variants ("Peng and Robinson", "Peng & Robinson",
"van-der-Waals", "RKS", "Cattoën" written "Cattoen", camelCase `pengRobinson`), and two of its backings are
loose: `reading` accepts ANY literal reading registered for the headline as backing for "printed" or
"Eq. (n)", and `source` accepts a reading registered with `source=<Name>` without asking whether the reader
attributed anything to that name.

  python3 scripts/trust/check_source_variants.py              rules V1-V3 on the current tree
  python3 scripts/trust/check_source_variants.py --base SHA   also V4
  python3 scripts/trust/check_source_variants.py --report     print every unbacked match, never fail

V1 (normalised matching): each headline's docstring and name are normalised — lower case, diacritics removed,
   hyphens/dashes/apostrophes/`&`/`+`/`/` and the word "and" turned into spaces, possessive `'s` dropped,
   camelCase and `_` split, whitespace collapsed — and every alias of `scripts/trust/source_aliases.txt`
   (`<key> | <aliases> | <backing>`, `=` for the key's backing in source_names.txt) is matched as a whole-word
   sequence. The `printed` and `equation-number` entries of source_names.txt are matched by their regexes as
   before. A match must be backed by one alternative of the key's backing (same syntax: fixed:, reach:,
   kind:, source, reading), with the two backings below read strictly.
V2 (`source`, strict): backed if (a) the statement reaches a PRINTED or CLAIM definition whose name or
   docstring contains the name (normalised), or (b) a literal reading is registered for THIS headline in
   literal_readings.txt with `source=<S>`, S normalised equal to or containing the matched name, AND at
   least one reader constant of that registration names it in the blind reader's own file (the code-identical
   `runs/` copy of its module: the constant's docstring or the module doc there, not the Checked copy whose
   docs authors may rewrite).
V3 (`reading`, strict): "printed"/"misprint"/"as published" is backed by a registered reading only if one of the
   headline's registered constants is described in its own docstring in the reader's own runs/ file with
   "print", "table", "published" or "reference value"; "Eq. (n)" / "(N.M)" only if that equation number occurs in the reader's
   own runs/ file or in a brief of its folder written as a citation (`Eq. n`, `Equation n`, `(n)`).
Unbacked matches that check_source_names.py already grandfathers (`source_names_baseline.txt`, same headline
and key) pass here too; new ones found by these stricter rules on the tree at 6fc653c are listed in the
shrink-only `scripts/trust/source_variants_baseline.txt` (`<headline> <key>  # reason`).
V4 (--base): source_variants_baseline.txt may not grow; source_aliases.txt may not lose or change a line.

Limits: a name absent from both registries is not read (add aliases with the first headline that uses one);
the backing shows that the reader or a reached transcription NAMES the source, not that the source says what
the docstring says; abbreviations shorter than two letters and names in other scripts are not matched.
"""
import re
import sys
import unicodedata
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_provenance as P  # noqa: E402
import check_literals as L  # noqa: E402
import check_source_names as S  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]
ALIASES = "scripts/trust/source_aliases.txt"
BASELINE = "scripts/trust/source_variants_baseline.txt"
OLD_BASELINE = "scripts/trust/source_names_baseline.txt"
REGEX_KEYS = {"printed", "equation-number"}


def normalise(s):
    s = unicodedata.normalize("NFKD", s)
    s = "".join(c for c in s if not unicodedata.combining(c))
    s = re.sub(r"([a-z0-9])([A-Z])", r"\1 \2", s)
    s = re.sub(r"([A-Z]+)([A-Z][a-z])", r"\1 \2", s)
    s = s.lower()
    s = re.sub(r"['’]s\b", "", s)
    s = re.sub(r"[_\-–—‐‑&+/'’`]", " ", s)
    s = re.sub(r"\band\b", " ", s)
    s = re.sub(r"[^a-z0-9]+", " ", s)
    return " " + " ".join(s.split()) + " "


def load_aliases(errors, base_reg):
    out = []
    for l in L.entries(ALIASES) or []:
        ps = [x.strip() for x in l.split("|")]
        if len(ps) != 3:
            errors.append(f"{ALIASES}: malformed line {l[:80]}")
            continue
        key, al, back = ps
        if back == "=":
            if key not in base_reg:
                errors.append(f"{ALIASES}: {key} has backing `=` but no line in {S.REG}")
                continue
            alts = base_reg[key]
        else:
            alts = [[q.strip() for q in a.split("+") if q.strip()] for a in back.split("||")]
        aliases = [" " + " ".join(normalise(a).split()) + " " for a in al.split(",") if a.strip()]
        out.append((key, aliases, alts))
    return out


_RUNS_TEXT = {}


def reader_text(const_rel):
    """the blind reader's own file(s) (runs/ copies of the module) and the briefs of their folders"""
    if const_rel not in _RUNS_TEXT:
        own, briefs = "", ""
        for c in P.runs_copies(P.code((ROOT / const_rel).read_text())):
            own += (ROOT / c).read_text(errors="replace")
            for f in (ROOT / c).parent.iterdir():
                if f.is_file() and f.suffix == ".md" and re.search(r"brief", f.name, re.I):
                    briefs += f.read_text(errors="replace")
        _RUNS_TEXT[const_rel] = (own, briefs)
    return _RUNS_TEXT[const_rel]


def const_doc(own, full, moddoc=True):
    """docstring of `full`'s last component in the reader's own file (plus its module doc if `moddoc`)"""
    last = full.split(".")[-1]
    m = re.search(r"/--((?:(?!-/).)*)-/\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:def|abbrev)\s+" + re.escape(last)
                  + r"(?![\w'])", own, re.S)
    mod = " ".join(re.findall(r"/-!(.*?)-/", own, re.S))
    return (m.group(1) if m else "") + (" " + mod if moddoc else "")


def strict_backed(part, key, matched, row, defs_rows, readings, consts):
    if part not in ("source", "reading"):
        return S.backed(part, matched, row, defs_rows, readings)
    nm = " " + " ".join(normalise(matched).split()) + " "
    regs = readings.get(row["name"], [])
    if part == "source":
        reached = dict(row.get("defs", {}))
        for d, k in reached.items():
            if k in ("PRINTED", "CLAIM") and (nm in normalise(d) or nm in normalise(defs_rows.get(d, {}).get("doc", ""))):
                return True
        for c, srcs in regs:
            if not any(nm.strip() in normalise(s) for s in srcs) or c not in consts:
                continue
            own, _ = reader_text(consts[c][2])
            if nm in normalise(const_doc(own, c)):
                return True
        return False
    # reading (V3)
    for c, _ in regs:
        if c not in consts:
            continue
        own, briefs = reader_text(consts[c][2])
        if key == "printed":
            if re.search(r"(?i)print|table|published|reference value", const_doc(own, c, moddoc=False)):
                return True
        elif key == "equation-number":
            nums = re.findall(r"\d+(?:\.\d+)?|[A-Z]\d{1,2}", matched)
            if nums and all(re.search(r"(?:\bEqs?\.?\s*|\bEquations?\s*)\(?" + re.escape(n) + r"\)?(?![\d.])|\(" + re.escape(n)
                                      + r"\)", own + briefs) for n in nums):
                return True
        elif nm in normalise(own):
            return True
    return False


def violations(rows, aliases, base_reg_rx, readings, consts):
    defs_rows = {r["name"]: r for r in rows if r.get("type") == "def"}
    out = []
    for row in rows:
        if row.get("type") != "headline":
            continue
        raw = [row.get("doc", ""), S.name_words(row["name"])]
        text = normalise(" ".join(raw))
        for key, als, alts in aliases:
            for a in als:
                if a in text:
                    if not any(all(strict_backed(p, key, a.strip(), row, defs_rows, readings, consts) for p in alt)
                               for alt in alts):
                        out.append((row["name"], key, a.strip()))
                        break
        for key, rx, alts in base_reg_rx:
            if key not in REGEX_KEYS:
                continue
            hits = sorted({m.group(0) for t in raw for m in rx.finditer(t)})
            for h in hits:
                if not any(all(strict_backed(p, key, h, row, defs_rows, readings, consts) for p in alt) for alt in alts):
                    out.append((row["name"], key, h))
                    break
    return out


def pairs(text):
    out = set()
    for l in (text or "").splitlines():
        l = l.split("#")[0].split()
        if len(l) >= 2:
            out.add((l[0], l[1]))
    return out


def main():
    base = sys.argv[sys.argv.index("--base") + 1] if "--base" in sys.argv else None
    report = "--report" in sys.argv
    rows = L.load_rows()
    if rows is None:
        print("check_source_variants: .lake/meaning.jsonl missing (run StatementDeps.lean first)")
        return 0 if report else 1
    heads = {r["name"] for r in rows if r.get("type") == "headline"}
    errors = []
    reg = S.load_reg(errors)
    base_reg = {k: alts for k, _, alts in reg}
    aliases = load_aliases(errors, base_reg)
    readings = L.load_readings(heads, [])
    consts = L.reader_constants()
    viol = violations(rows, aliases, reg, readings, consts)
    old_bl = pairs((ROOT / OLD_BASELINE).read_text() if (ROOT / OLD_BASELINE).exists() else "")
    bl = pairs((ROOT / BASELINE).read_text() if (ROOT / BASELINE).exists() else "")
    seen = set()
    for h, key, hit in viol:
        seen.add((h, key))
        if report:
            print(f"{h} {key}  # '{hit}'{' (old baseline)' if (h, key) in old_bl else ''}")
        elif (h, key) not in old_bl and (h, key) not in bl:
            errors.append(f"{h}: '{hit}' ({key}) in its docstring or name is not backed (V1-V3): name the source "
                          f"through a reached PRINTED/CLAIM definition or a reading registered for this headline whose "
                          f"reader names it")
    for b in sorted(bl - seen):
        errors.append(f"{BASELINE}: {b[0]} {b[1]} is backed now (or gone); remove the line (shrink-only)")
    for b in sorted(bl & old_bl):
        errors.append(f"{BASELINE}: {b[0]} {b[1]} duplicates a line of {OLD_BASELINE}; remove it here")
    if base:
        old = P.git("show", f"{base}:{BASELINE}")
        if old is not None:
            for b in sorted(bl - pairs(old)):
                errors.append(f"{BASELINE} grew against {base}: {b} (it may only shrink)")
        olda = P.git("show", f"{base}:{ALIASES}")
        if olda is not None:
            now = set(L.entries(ALIASES) or [])
            for l in olda.splitlines():
                l = l.split("#")[0].rstrip()
                if l.strip() and l not in now:
                    errors.append(f"{ALIASES}: line removed or changed against {base}: {l[:80]} (may only grow)")
    if report:
        print(f"check_source_variants: {len(viol)} unbacked (report only)")
        return 0
    for e in errors:
        print(e)
    print(f"check_source_variants: {len(aliases)} alias lines, {len(viol)} unbacked matches "
          f"({len(seen & old_bl)} in {Path(OLD_BASELINE).name}, {len(bl)} baselined here); {'FAIL' if errors else 'ok'}")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
