"""Generate every phrase of scripts/trust/phrases.txt from the blind registry (run 2026-11-09T0228Z, rules P7/P9).
Shape (value definitions): the NAME with the ROLE {x}, the ROLE {y} and the ROLE {z} (SIGN; …; CLAUSE; …)
Shape (predicates): the ROLE {s}[, … and the ROLE {s'}] VERB the NAME with the ROLE {x}, … (SIGN; …; CLAUSE; …)
The only author choices left: which binders are the subject of a predicate, its verb and article, and the exclusion
baseline scripts/trust/phrase_clause_baseline.txt (reader lines not shown: ambiguous plain-words parse, a hypothesis of
the specification rather than a property of the definition, a duplicate, or false at junk values; reasons below)."""
import re, sys
sys.path.insert(0, "scripts/trust")
import check_claims as cc

# predicate shapes: definition -> (subject binders, verb, article before NAME)
PRED = {
    "Aviles.IsFlatLCDM": (["a"], "obeys", "the"),
    "CPL.IsFlatCPL": (["a"], "obeys", "the"),
    "FRCosmo.FriedmannEq": ([], "holds", "the"),
    "FRCosmo.MasterEq": ([], "holds", "the"),
    "CubicEOS.IsCriticalIsotherm": (["p"], "satisfies", "the"),
    "Coexistence.IsMaxwellCoexistence": (["p"], "satisfies", "the"),
    "Duffing.IsDuffingSolution": (["x"], "is", "a"),
    "MichaelisMenten.IsMMSolution": (["s", "e", "c", "p"], "are", "a"),
    "Robertson.IsRobSolution": (["y₁", "y₂", "y₃"], "are", "a"),
}


def slots(text, binders):
    for x in sorted(binders, key=len, reverse=True):
        if x == "a":
            text = re.sub(r"\bcurv of a$", "curv of {a}", text)
            continue
        pat = r"(?<![\w{])" + re.escape(x) + r"(?![\w}])"
        if x == "F":
            pat += r"(?! of R gravity)"
        text = re.sub(pat, "{" + x + "}", text)
    return text


def listing(items):
    return items[0] if len(items) == 1 else ", ".join(items[:-1]) + " and " + items[-1]


def main():
    reg = open(cc.ROOT / cc.ROLES, encoding="utf-8").read()
    roles, signs, clauses, bad = cc.load_registry(reg)
    names = cc.registry_names(reg)
    assert not bad, bad
    lines = open(cc.ROOT / cc.PHR, encoding="utf-8").read().splitlines()
    out = []
    for l in lines:
        if not l.strip() or l.startswith("#") or " | " not in l:
            out.append(l)
            continue
        d = l.split(" | ", 1)[0].strip()
        key = cc._full(d, roles)
        rmap = roles[key]
        name = names[key][0]
        nm = [n for n in signs.get(key, []) if n == name]
        sg = [x for x in signs.get(key, []) if x != name]
        par = []
        for x in [slots(x, rmap) for x in sg + clauses.get(key, [])]:
            if any(f" {x} " in f" {y} " for y in par):
                continue  # a blind text already shown inside another (curvK: SIGN and CLAUSE)
            if par and x.startswith("divided by "):
                par[-1] += " " + x  # the reader split one quotient into two clauses (decel, cosmoCoeff)
            else:
                par.append(x)
        tail = f" ({'; '.join(par)})" if par else ""
        if d in PRED:
            subj, verb, art = PRED[d]
            rest = [b for b in rmap if b not in subj]
            s = listing([f"the {rmap[b]} {{{b}}}" for b in subj]) + " " if subj else ""
            ph = f"{s}{verb} {art} {name}" if subj else f"the {name} {verb}"
            if rest:
                ph += " with " + listing([f"the {rmap[b]} {{{b}}}" for b in rest])
        else:
            ph = f"the {name} with " + listing([f"the {rmap[b]} {{{b}}}" for b in rmap])
        out.append(f"{d} | {ph}{tail}")
    open(cc.ROOT / cc.PHR, "w", encoding="utf-8").write("\n".join(out) + "\n")


main()
