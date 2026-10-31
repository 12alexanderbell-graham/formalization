#!/usr/bin/env python3
"""Meaning carried by prose and names (trust track T2c, run 2026-10-31T1028Z). Blocking in CI.

The kernel checks statements; a scientist reads names and docstrings. Red teams of a different
model (runs 0028Z, 0228Z) passed four wrong claims through every check by putting the meaning in
prose: a new definition *named* and *described* as a physical quantity but built from something
else (A04, B04), an existential theorem described as a general law (A05), and a certified number
computed from a free formula with a docstring describing another one (D04). This script checks
what the prose may say against what the Lean statement actually contains, using the facts that
`scripts/trust/StatementDeps.lean` writes to `.lake/meaning.jsonl`:

1. Vocabulary (glossary `scripts/trust/glossary.txt`): a meaning-bearing term in the docstring of a
   headline must be backed by a pinned definition the statement reaches, or whose defining law
   (an equation in its body over other pinned definitions) the statement writes out verbatim up to
   variable names (`laws`, run 1028Z: B1 states the flat ΛCDM Friedmann law on an interval); in the docstring of a
   definition a headline rests on, by a pinned definition that the definition or one of the
   headlines using it reaches.
2. Names: a definition a headline rests on, other than the pinned definition itself, may not carry
   a pinned definition's name inside its own (`angDistEth`, `lumDistEdS`).
3. Shape: a headline whose conclusion is an existence statement says so in words; one that asserts
   only negations (refutations) says so; one with no universally bound data does not say "every",
   "any", "all", "general".
4. Records: a `Checked.Records` headline (a certified number) rests on at least one pinned or
   transcribed (PRINTED/CLAIM) definition: a number about a free formula certifies nothing about
   the physics (D04).

Run after `lake env lean scripts/trust/StatementDeps.lean`. `--report` prints without failing.
"""
import json, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
EXIST = re.compile(r"(?i)\b(exist\w*|there (is|are)|some|admits?|witness\w*|instances?|examples?|exactly one|unique\w*|can be)\b")
NEG = re.compile(r"(?i)\b(not|no|false|fails?|failure|wrong|refut\w*|misprint\w*|differs?|incorrect|never|miss(es)?|nonzero|non-zero|cannot|impossible|inconsistent)\b|≠|¬")
UNIV = re.compile(r"(?i)\b(every|any|all|each|general(ly)?|whenever|always|universal(ly)?)\b")

def short(n):
    return n.split(".")[-1]

def tokens(name):
    """camelCase / snake_case tokens of a name's last component"""
    return [t for t in re.findall(r"[A-Z]+(?![a-z])|[A-Z]?[a-z]+|[0-9]+", short(name))]

def contains_run(hay, needle):
    return any(hay[i:i + len(needle)] == needle for i in range(len(hay) - len(needle) + 1))

KNOWN = set()

def strip_code_names(doc):
    """docstrings may *name* Lean constants in backticks (`printedD3y_fails_past`); a backticked
    name of a program constant is a reference, not a description, so it is not read. Everything
    else (formulas such as `d_L`, `D⁴_L`) is read."""
    def keep(m):
        t = m.group(1)
        return "``" if (t in KNOWN or short(t) in KNOWN) else m.group(0)
    return re.sub(r"`([A-Za-z_][A-Za-z0-9_.']*)`", keep, doc)

def main():
    report = "--report" in sys.argv
    rows = [json.loads(l) for l in (ROOT / ".lake/meaning.jsonl").read_text().splitlines() if l.strip()]
    gloss = []
    for l in (ROOT / "scripts/trust/glossary.txt").read_text().splitlines():
        if not l.strip() or l.startswith("#"):
            continue
        rx, backs = l.split(" => ")
        gloss.append((rx, re.compile(rx), set(backs.split())))
    pinned = {short(r["name"]) for r in rows if r["type"] == "pinned"}
    pinned_full = {r["name"] for r in rows if r["type"] == "pinned"}
    for _, _, backs in gloss:
        for b in backs:
            if b not in pinned:
                sys.exit(f"glossary backs a term by {b}, which is not a pinned definition")
    heads = {r["name"]: r for r in rows if r["type"] == "headline"}
    KNOWN.update(short(r["name"]) for r in rows)
    KNOWN.update(r["name"] for r in rows)
    errs = []

    def vocab(owner, doc, reached):
        text = strip_code_names(doc)
        have = {short(p) for p in reached}
        for rx, c, backs in gloss:
            m = c.search(text)
            if m and not (backs & have):
                errs.append((f"{owner}|vocab|{rx}", f"{owner}: its docstring says '{m.group(0)}' but the statement reaches none of "
                            f"the pinned definitions {sorted(backs)} that give that term its meaning "
                            f"(reaches: {sorted(have) or 'no pinned definition'})"))

    for h in heads.values():
        doc = h["doc"]
        vocab(h["name"], doc, h["pinned"] + h.get("laws", []))
        shapes = h["shapes"]
        if "EXISTS" in shapes and not EXIST.search(doc):
            errs.append((f"{h['name']}|exists", f"{h['name']}: the statement asserts existence (∃) but the docstring does not say so "
                        f"(write 'there is', 'exists', 'some', 'an example', ...)"))
        if shapes and all(s == "NOT" for s in shapes) and not NEG.search(doc):
            errs.append((f"{h['name']}|negation", f"{h['name']}: the statement is a negation (refutation) but the docstring does not say so"))
        if not h["universal"]:
            m = UNIV.search(strip_code_names(doc))
            if m:
                errs.append((f"{h['name']}|universal", f"{h['name']}: the docstring says '{m.group(0)}' but the statement binds no "
                            f"universally quantified data, even inside its claims (it is about fixed objects)"))
        if h["record"]:
            kinds = set(h["defs"].values())
            if (not h["pinned"] and not (kinds & {"PRINTED", "CLAIM"})) or h.get("free_conjuncts", 0) > 0:
                errs.append((f"{h['name']}|free-record", f"{h['name']}: a certified number about a free formula: the record reaches no pinned "
                            f"or transcribed definition, so nothing ties its formula to the physics it names"))
    for r in rows:
        if r["type"] != "def":
            continue
        reached = set(r["pinned"])
        for u in r["users"]:
            reached |= set(heads[u]["pinned"] + heads[u].get("laws", [])) if u in heads else set()
        vocab(f"definition {r['name']} ({r['kind']})", r["doc"], reached)
        if r["name"] in pinned_full:
            continue
        for p in pinned:
            if p != short(r["name"]) and contains_run(tokens(r["name"]), tokens(p)) and len(tokens(p)) >= 1 \
                    and len(p) >= 4:
                errs.append((f"definition {r['name']}|name|{p}", f"definition {r['name']} ({r['kind']}) carries the pinned definition name '{p}' "
                            f"in its own name but is not that definition: rename it (names carry meaning to readers)"))
    # ratchet (run 2026-10-31T1028Z): problems present when the check was introduced are listed in
    # scripts/trust/prose_baseline.txt (known gaps, shown here); the baseline may only shrink and the
    # glossary may only grow (both checked against the base commit with --base)
    bpath = ROOT / "scripts/trust/prose_baseline.txt"
    if "--write-baseline" in sys.argv:
        bpath.write_text(BASELINE_HEAD + "".join(k + "\n" for k in sorted({k for k, _ in errs})))
        print(f"baseline written: {len({k for k, _ in errs})} keys")
        return
    base = {l for l in bpath.read_text().splitlines() if l and not l.startswith("#")}
    new = [(k, m) for k, m in errs if k not in base]
    known = sorted({k for k, _ in errs if k in base})
    print(f"check_prose: {len(heads)} headlines, {sum(r['type'] == 'def' for r in rows)} definitions, "
          f"{len(gloss)} glossary terms; {len(new)} new problems; {len(known)} known gaps (prose_baseline.txt)")
    for _, m in new:
        print("  " + m)
    stale = sorted(base - {k for k, _ in errs})
    if stale:
        print(f"  baseline entries now fixed (remove them from prose_baseline.txt): {len(stale)}")
        for k in stale:
            print("    " + k)
    fail = bool(new) or bool(stale)
    if "--base" in sys.argv:
        import subprocess
        b = sys.argv[sys.argv.index("--base") + 1]
        def old(rel):
            r = subprocess.run(["git", "show", f"{b}:{rel}"], cwd=ROOT, capture_output=True, text=True)
            return None if r.returncode else r.stdout
        ob, og = old("scripts/trust/prose_baseline.txt"), old("scripts/trust/glossary.txt")
        if ob is not None:
            grown = base - {l for l in ob.splitlines() if l and not l.startswith("#")}
            if grown:
                # growth only when a check is strengthened (new rule, new glossary term) and disclosed:
                # every new key's constant named in a LEDGER.md addition of the same push
                r = subprocess.run(["git", "diff", b, "HEAD", "--", "LEDGER.md"], cwd=ROOT, capture_output=True, text=True)
                added = "\n".join(l for l in r.stdout.splitlines() if l.startswith("+"))
                undisclosed = sorted(k for k in grown if short(k.split("|")[0].replace("definition ", "").split(" ")[0]) not in added)
                if undisclosed:
                    print(f"prose_baseline.txt grew against {b} without a LEDGER.md addition naming: {undisclosed} "
                          f"(the baseline may only shrink, except when a strengthened check finds old gaps; name them)")
                    fail = True
        if og is not None:
            gnow = set((ROOT / "scripts/trust/glossary.txt").read_text().splitlines())
            lost = [l for l in og.splitlines() if l and not l.startswith("#") and l not in gnow]
            if lost:
                print(f"glossary.txt lost or changed terms against {b}: {lost} (the glossary may only grow)")
                fail = True
    if fail and not report:
        sys.exit(1)

BASELINE_HEAD = """# Known prose/meaning gaps when the check was introduced (run 2026-10-31T1028Z), one key per line.
# Generated by: python3 scripts/trust/check_prose.py --write-baseline. May only shrink (CI --base),
# except new keys named in a LEDGER.md addition of the same push (a strengthened check finding old gaps);
# a fixed gap must be removed. Keys: <constant>|<rule>[|<term>].
"""

if __name__ == "__main__":
    main()
