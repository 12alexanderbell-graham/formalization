#!/usr/bin/env python3
"""Claim templates of generated readings are frozen (run 2026-11-06T0228Z, part 3; written blind to red team M).
Blocking in CI.

Why: `scripts/trust/gen_claim_readings.py` substitutes a blind reader's DATA into the text of a program CLAIM;
the quantifiers, hypotheses, filters, remainder templates and relation of the claim are the program's own and
are copied into the second version unchanged. A data reading therefore covers nothing outside the substituted
regions: a narrowed or widened hypothesis written into the program claim itself (round L, d04 re-routed) is
"read twice" as far as every other check can see. This script freezes the template — the claim with the
substituted regions masked — of every claim that has a generated reading.

  python3 scripts/trust/check_templates.py              rule 1 on the current tree
  python3 scripts/trust/check_templates.py --base SHA   also rule 2 against SHA (CI: the push's before-SHA)
  python3 scripts/trust/check_templates.py --show NAME  print the masked template of a claim

Template of a claim P with generated reading G (agreement `P = G` in `Checked/Trust/TranscriptionsClaims.lean`):
  the token sequence of P's declaration after `:=` (comments stripped, tokens as check_provenance.py rule 2) in
  which every maximal run of tokens that differs from G (difflib opcodes) is replaced by one `□`. Everything
  the reader did not supply is in the template, verbatim.
Rule 1: every such claim has a line `<claim full name> <sha256 of the template, 16 hex>` in
  `scripts/trust/claim_templates.txt` with the current hash, and every line names such a claim.
Rule 2 (--base): a line added to, changed in or removed from `claim_templates.txt` against SHA needs a
  LEDGER.md line (added since SHA) naming the claim's last name component and the word "template" — EXCEPT an
  added line whose hash equals the hash of a line already present at SHA (a new instance of a frozen template:
  same quantifiers, hypotheses and relation, only reader data differ). A narrowed hypothesis in a new claim
  produces a new template and so cannot pass silently; a changed template of an existing claim fires rule 1.

Populated at run 2026-11-06T0228Z with the 30 claims then read (none grandfathered: every current claim
is registered with its current template). Limits: the template is frozen, not validated — that it says what
the source says is the business of the claim's blind restatement (not mechanically linked here); a template
change disclosed in LEDGER passes.
"""
import difflib
import hashlib
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_provenance as P  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]
REG = "scripts/trust/claim_templates.txt"


def claim_pairs(errors):
    """[(program claim full name, program decl text, generated decl text)]"""
    gtext = (P.TRUST / P.GENERATED[0]).read_text()
    gdecls, _ = P.declarations(gtext)
    gnames = {f for f, _, _ in gdecls}
    idx = P.program_index()
    kinds = {}
    for l in P.entries("scripts/trust/def_kinds.txt") or []:
        ps = l.split()
        if len(ps) == 2:
            kinds[ps[0]] = ps[1]
    out = []
    for rel, thm, prog, sec in P.agreements():
        g = [s for s in sec if s in gnames]
        if not g or len(prog) != 1:
            continue
        p = prog[0]
        if kinds.get(p) != "CLAIM":
            continue
        loc = idx.get(p)
        if loc is None:
            errors.append(f"rule 1: {p} not found in a Checked module")
            continue
        ptext = (ROOT / loc).read_text()
        pd = P.decl_text(ptext, p, P.declarations(ptext)[0])
        gd = P.decl_text(gtext, g[0], gdecls)
        if pd is None or gd is None:
            errors.append(f"rule 1: cannot read {p} / {g[0]}")
            continue
        out.append((p, pd, gd))
    return out


def template(pd, gd):
    pt = P.tokens(pd.split(":=", 1)[1]) if ":=" in pd else P.tokens(pd)
    gt = P.tokens(gd.split(":=", 1)[1]) if ":=" in gd else P.tokens(gd)
    sm = difflib.SequenceMatcher(a=pt, b=gt, autojunk=False)
    out = []
    for op, i1, i2, j1, j2 in sm.get_opcodes():
        if op == "equal":
            out += pt[i1:i2]
        elif not out or out[-1] != "□":
            out.append("□")
    return out


def digest(tpl):
    return hashlib.sha256(" ".join(tpl).encode()).hexdigest()[:16]


def parse(text):
    out = {}
    for l in text.splitlines():
        l = l.split("#")[0].strip()
        if l:
            ps = l.split()
            if len(ps) >= 2:
                out[ps[0]] = ps[1]
    return out


def main():
    errors = []
    pairs = claim_pairs(errors)
    if "--show" in sys.argv:
        nm = sys.argv[sys.argv.index("--show") + 1]
        for p, pd, gd in pairs:
            if p == nm or p.endswith("." + nm):
                print(p, digest(template(pd, gd)))
                print(" ".join(template(pd, gd)))
        return 0
    if "--write" in sys.argv:  # used once to populate the registry (run 2026-11-06T0228Z)
        hdr = [l for l in (ROOT / REG).read_text().splitlines() if l.startswith("#")] if (ROOT / REG).exists() else []
        (ROOT / REG).write_text("\n".join(hdr + [f"{p} {digest(template(pd, gd))}" for p, pd, gd in sorted(pairs)]) + "\n")
        return 0
    base = sys.argv[sys.argv.index("--base") + 1] if "--base" in sys.argv else None
    reg = parse((ROOT / REG).read_text()) if (ROOT / REG).exists() else None
    if reg is None:
        errors.append(f"rule 1: {REG} is missing")
        reg = {}
    have = set()
    for p, pd, gd in pairs:
        have.add(p)
        h = digest(template(pd, gd))
        if p not in reg:
            errors.append(f"rule 1: {p} has a generated reading but no frozen template in {REG} "
                          f"(template {h}; see --show; rule 2 decides whether it may be added)")
        elif reg[p] != h:
            errors.append(f"rule 1: the template of {p} changed ({reg[p]} -> {h}): its quantifiers, hypotheses or "
                          f"relation differ from the frozen ones")
    for p in sorted(set(reg) - have):
        errors.append(f"rule 1: {REG} lists {p}, which has no generated reading")
    if base:
        old = P.git("show", f"{base}:{REG}")
        if old is not None:
            o = parse(old)
            led = [l for l in P.ledger_added(base).splitlines() if re.search(r"template", l, re.I)]
            for p in sorted(set(o) | set(reg)):
                if o.get(p) == reg.get(p):
                    continue
                if p not in o and reg[p] in set(o.values()):
                    continue  # a new instance of a frozen template
                short = p.split(".")[-1]
                if not any(re.search(r"(?<![\w.])" + re.escape(short) + r"(?![\w])", l) for l in led):
                    errors.append(f"rule 2: {REG}: {p} added, changed or removed against {base} with a new template, "
                                  f"without a LEDGER.md addition naming {short} and the word 'template'")
    for e in errors:
        print(e)
    print(f"check_templates: {len(pairs)} claims with generated readings, {len(reg)} frozen templates "
          f"({len(set(reg.values()))} distinct); {'FAIL' if errors else 'ok'}")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
