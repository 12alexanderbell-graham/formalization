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
5. Numbers (run 2026-11-04T0828Z; blocking since run 2026-11-04T1028Z, old gaps baselined per number,
   so a changed number fires again): every decimal (`2.5665`) or fraction (`13/5`) in a headline docstring is a numeric
   literal of the statement (numeral, decimal, or quotient of two), as `nums` in meaning.jsonl.
   A simulation or computation whose docstring names a time, bound or value the statement does
   not contain is a wrong claim no other check reads (part 3, "wrong simulation" class).
   Since run 2026-11-04T1428Z (red team H, blind): an unsigned number that matches only a negative
   literal needs a sign or "minus"/"negative" just before it (d05), and a citation `(N.M)` passes only
   for the headlines registered with it in `scripts/trust/citation_owners.txt` (d08 wrote a value as
   "(1.9)", a number registered because another headline cites Eq. (1.9)).
7. Module docs (run 2026-11-04T1428Z; red team H, d06): every decimal or fraction in the `/-! -/`
   doc of a Checked file is a numeric literal of a headline stated in that file (or a citation
   registered for one of them); the 499 numbers of the module docs at d714f04 are baselined per
   number (frozen docs: a changed number fires again).
6. Parameters (run 2026-11-04T1428Z; red team G, defect G02, class E08: a correct wrapper headline
   said its bracket holds "whatever the release amplitude" while the statement fixes x(0) = 1). After
   every generalising word (every, any, all, each, whatever, whichever, regardless of, irrespective
   of, independent(ly) of, does not depend on, no matter, arbitrary, uniform(ly), for all) the
   phrase that follows (up to `. ; :`, a dash, an unbracketed comma, or 8 words; split at `and`/`or`
   into parts) must, in its first part, name something the statement universally binds (through `∀`,
   `→`, `∧`, `↔`, inside `∃` bodies and under `¬`, not the `∃` variable itself): a bound variable by
   its Lean name (subscripts read as digits, `Ω_M` as `Ω`; a one-letter English word such as `a`
   only inside backticks or alone), or a noun registered in `scripts/trust/param_nouns.txt` for a
   role a bound variable fills (`Def.binder`: the variable is passed as that explicit argument), a
   bound variable's type (`type:`) or name (`name:`). A part whose first two words, or any later
   part, or a first part naming nothing bound, contains a noun registered for a role the statement
   fixes to a number is reported with that number. "all three …" (an enumeration) is skipped.
   Known limits: later conjuncts are read only for registered fixed-parameter nouns (an
   unregistered synonym after "and" passes); generality expressed without a generalising word
   ("independent of the amplitude" is caught; "amplitude-independent" and "isochronous" are not). StatementDeps writes `bound`, `roles` and `fixed` to meaning.jsonl;
   TRUST_MAP.md and the packet show the fixed parameters (generated). The noun registry may only
   grow, each addition disclosed by a LEDGER.md addition naming the noun (`--base`). Parts with no
   word of two or more letters (pure mathematics: `> 0`) pass.
4. Records: a `Checked.Records` headline (a certified number) rests on at least one pinned or
   transcribed (PRINTED/CLAIM) definition: a number about a free formula certifies nothing about
   the physics (D04).

Run after `lake env lean scripts/trust/StatementDeps.lean`. `--report` prints without failing.
"""
import fnmatch, json, re, sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
EXIST = re.compile(r"(?i)\b(exist\w*|there (is|are)|some|admits?|witness\w*|instances?|examples?|exactly one|unique\w*|can be)\b")
NEG = re.compile(r"(?i)\b(not|no|false|fails?|failure|wrong|refut\w*|misprint\w*|differs?|incorrect|never|miss(es)?|nonzero|non-zero|cannot|impossible|inconsistent)\b|≠|¬")
NUM = re.compile(r"(?<![\w.^⁻/])((?:(?<![\d)])[-−])?)(\d+(?:\.\d+)?\s*[×x]\s*10[⁻⁺]?[⁰¹²³⁴⁵⁶⁷⁸⁹]+|\d+\.\d+|\d+/\d+)(?![\d/]|\.\d)")
# a unit glued to a number (`0.1mM`, `2.5665s`) does not hide it (red team G, d01, run 2026-11-04T1028Z):
# the lookahead excludes only digits, `/` and a further decimal part, not letters
SUP = str.maketrans("⁰¹²³⁴⁵⁶⁷⁸⁹⁻⁺", "0123456789-+")
# citations are not values (run 2026-11-04T1028Z: 54 of the 81 first-report items were equation
# numbers): `(10.54)`, `(10.56)–(10.57)`, `Eq. 10.54`, `Eqs. (11.42)–(11.43)`, `annex 40.1`, `Sec. 2.3`.
# A parenthesised number counts as a citation only in equation-number shape (integer part 1–99, one or
# two decimals) and only when no comparison or assignment sign precedes the parenthesis (`t ≈ (2.57)` is
# a value). Residual hole, recorded in LEDGER: a two-decimal value written alone in parentheses.
CITE = re.compile(r"(?:(?<![=≈<>≤≥±~∈]\s)(?<![=≈<>≤≥±~∈])\((?:[1-9]\d?\.\d{1,2})\)(?:\s*[–-]\s*\((?:[1-9]\d?\.\d{1,2})\))?)"
                  r"|(?:\b(?:Eqs?\.|Equations?|annex|Annex|Sec\.|Section|Table|Fig\.)\s*\(?[1-9]\d?\.\d{1,2}\)?(?:\s*[–-]\s*\(?[1-9]\d?\.\d{1,2}\)?)?)")

CITED = []  # (owner, equation number) of every citation read (registry check in main)

def strip_citations(doc, owner=None):
    """blank citations; record their equation numbers: a citation passes only if its number is in
    scripts/trust/citations.txt (red team G, d08, run 2026-11-04T1028Z, wrote a wrong table value as
    `(2.77)`); the registry may grow only with a LEDGER.md addition naming the new number (--base)"""
    def blank(m):
        for n in re.findall(r"[1-9]\d?\.\d{1,2}", m.group(0)):
            if owner is not None:  # rule 6 re-reads docstrings without recording
                CITED.append((owner, n))
        return " " * len(m.group(0))
    return CITE.sub(blank, doc)

def num_value(tok):
    """value of a docstring number token: decimal, fraction, or m×10ⁿ (adversary, run 0828Z)"""
    m = re.match(r"(\d+(?:\.\d+)?)\s*[×x]\s*10([⁻⁺]?[⁰¹²³⁴⁵⁶⁷⁸⁹]+)$", tok)
    if m:
        return Fraction(m.group(1)) * Fraction(10) ** int(m.group(2).translate(SUP))
    return Fraction(tok)
UNIV = re.compile(r"(?i)\b(every|any|all|each|general(ly)?|whenever|always|universal(ly)?)\b")
# rule 6: words that generalise over what follows them
GEN = re.compile(r"(?i)\b(every|any|all|each|whatever|whichever|regardless\s+of|irrespective\s+of|independent(?:ly)?\s+of|"
                 r"(?:does|do|did)\s+not\s+depend\s+on|no\s+dependence\s+on|no\s+matter|arbitrary|uniform(?:ly)?(?:\s+(?:in|over|for))?|for\s+all)\b")
SUBS = str.maketrans("₀₁₂₃₄₅₆₇₈₉", "0123456789")
ENGLISH = {"a", "an", "as", "at", "be", "by", "in", "is", "it", "of", "on", "or", "to", "no", "I", "A"}

def gen_phrases(doc):
    """(trigger, parts) for every generalising word: the phrase after it up to `. ; :`, a dash, an
    unbracketed comma or 8 words, split at `and`/`or` (rule 6)"""
    out = []
    for m in GEN.finditer(doc):
        rest, depth, cut = doc[m.end():], 0, None
        for i, ch in enumerate(rest):
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                if depth == 0:
                    cut = i; break
                depth -= 1
            elif ch in ".;:—–" and depth == 0 and not (ch == "." and i + 1 < len(rest) and rest[i + 1].isdigit()):
                cut = i; break
            elif ch == "," and depth == 0:
                cut = i; break
            elif ch == "\n" and i + 1 < len(rest) and rest[i + 1] == "\n":
                cut = i; break
        phrase = rest[:cut] if cut is not None else rest
        words = phrase.split()
        phrase = " ".join(words[:8])
        parts = [q.strip() for q in re.split(r"\s+(?:and|or)\s+|\s+and/or\s+", phrase) if q.strip()]
        out.append((m.group(0), phrase, parts))
    return out

def norm_tok(s):
    return s.translate(SUBS).replace("′", "'").rstrip("'")


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

NOUNS = []  # (regex text, compiled, roles) from scripts/trust/param_nouns.txt

def load_nouns():
    path = ROOT / "scripts/trust/param_nouns.txt"
    if not path.exists():
        return
    for l in path.read_text(encoding="utf-8").splitlines():
        if not l.strip() or l.startswith("#"):
            continue
        rx, roles = l.split(" => ")
        NOUNS.append((rx, re.compile(rx), set(roles.split())))

FINITE = re.compile(r"(?i)^(two|three|four|five|six|seven|eight|nine|ten|both|\d+)\b")

def role_hit(pats, have):
    """does any role pattern (`Def.binder`, fnmatch wildcards) match a role in `have`"""
    return any(fnmatch.fnmatchcase(r, pat) for pat in pats if not pat.startswith(("type:", "name:")) for r in have)

def param_rule(h, errs):
    """rule 6: every generalising phrase names something the statement universally binds"""
    bound = {}
    for b in h["bound"]:
        n, _, ty = b.partition(" : ")
        bound.setdefault(norm_tok(n), set()).add(ty.strip())
    # a variable fixed by an equation hypothesis (`redshift a t₀ t₃ = 2 * √2 - 1`, role `=redshift=…`) does
    # not generalise: its roles count as fixed to that value (red team H, d04, run 2026-11-04T1428Z)
    eqfix = {}
    for v, r in h.get("roles", []):
        if r.startswith("="):
            eqfix.setdefault(norm_tok(v), []).append(r[1:].replace("=", " = ", 1))
    filled = {r for v, r in h.get("roles", []) if norm_tok(v) in bound and norm_tok(v) not in eqfix and not r.startswith("=")}
    fixed = {}
    for f in h.get("fixed", []):
        fixed.setdefault(f"{f['def']}.{f['param']}", []).append(f["lit"])
    for v, r in h.get("roles", []):
        if norm_tok(v) in eqfix and not r.startswith("="):
            fixed.setdefault(r, []).extend(e for e in eqfix[norm_tok(v)] if e not in fixed.get(r, []))
    def noun_ok(pats):
        if role_hit(pats, filled):
            return True
        for pat in pats:
            if pat.startswith("type:") and any(fnmatch.fnmatchcase(ty, pat[5:]) for tys in bound.values() for ty in tys):
                return True
            if pat.startswith("name:") and any(fnmatch.fnmatchcase(n, pat[5:]) for n in bound):
                return True
        return False
    def fixed_noun(part):
        for rx, c, pats in NOUNS:
            if c.search(part) and role_hit(pats, set(fixed)) and not noun_ok(pats):
                return sorted(r for r in fixed if role_hit(pats, {r}))
        return None
    def bound_ref(part):
        toks = re.findall(r"[\w′']+", part)
        words = [w for w in toks if sum(c.isalpha() for c in w) >= 2]
        if any(cand in bound and cand not in eqfix and (cand not in ENGLISH or len(words) == 0)
               for w in toks for cand in (norm_tok(w), norm_tok(w).split("_")[0])):
            return True
        # inside backticks a one-letter English word is mathematics (`a > 0` names the scale factor a)
        code = [w for s in re.findall(r"`([^`]+)`", part) for w in re.findall(r"[\w′']+", s)]
        if any(cand in bound and cand not in eqfix for w in code for cand in (norm_tok(w), norm_tok(w).split("_")[0])):
            return True
        return any(c.search(part) and noun_ok(pats) for _, c, pats in NOUNS)
    text = strip_citations(strip_code_names(h["doc"]))
    for trig, phrase, parts in gen_phrases(text):
        if trig.lower() == "all" and FINITE.match(phrase):
            continue  # "at all three redshifts": an enumeration of listed items, not a generalisation
        for i, part in enumerate(parts):
            key = f"{h['name']}|param|{trig.split()[0].lower()} {' '.join(part.split()[:2])}"
            # a fixed-parameter noun is reported when it leads the part, when the part names nothing bound,
            # and in every later conjunct ("every solution and amplitude")
            fx = fixed_noun(" ".join(part.split()[:2])) or fixed_noun(part)
            lead = fixed_noun(" ".join(part.split()[:2]))
            if fx and (lead or i > 0 or not bound_ref(part)):
                errs.append((key, f"{h['name']}: its docstring generalises '{trig} {part}', but the statement fixes "
                             + ", ".join(f"{r} = {'/'.join(fixed[r])}" for r in fx)
                             + " (TRUST_MAP.md, last column): the claim is proved for that value only"))
                continue
            if i > 0 or GEN.match(part):
                continue  # later conjuncts: only the fixed-parameter test (they may be clauses); a part that
                          # starts with its own generalising word is checked under that word
            toks = re.findall(r"[\w′']+", part)
            words = [w for w in toks if sum(c.isalpha() for c in w) >= 2]
            if not words and not any(norm_tok(w) in bound for w in toks):
                continue  # pure mathematics (`> 0`)
            if not bound_ref(part):
                errs.append((key, f"{h['name']}: its docstring generalises over '{trig} {part}', but the statement binds "
                             f"nothing it could refer to (bound: {sorted(bound) or 'nothing'}; nouns for bound roles: "
                             f"scripts/trust/param_nouns.txt)"))

def oreg_all():
    opath = ROOT / "scripts/trust/citation_owners.txt"
    return {tuple(l.split()) for l in opath.read_text(encoding="utf-8").splitlines() if l.strip() and not l.startswith("#")} if opath.exists() else set()

# data words (rule 8, run 2026-11-05T1428Z): a docstring or name that uses one claims something about
# data or a fit, which only a statement reaching a transcribed (PRINTED) table or source can carry
DATA = re.compile(r"(?i)\bfit(s|ted|ting)?\b|best[- ]?fit|\bdata(set)?\b|supernova|\bSNe?\b|\bSNe? ?Ia\b|"
                  r"Pantheon|\bUnion ?\d|\bJLA\b|\bPlanck\b|\bBAO\b|chronometer|\bquasars?\b|\bGRBs?\b|"
                  r"χ²|chi[- ]?squared?|\bchi ?Sq|\bchi2\b|likelihood|\bmeasure(d|ments?)\b|\bsurvey\b|"
                  r"\bcatalog(ue)?\b|\bobservations\b|\bCMB\b|\bWMAP\b|\bDESI\b|\bSDSS\b|\bSH0ES\b|"
                  r"Hubble diagram|\bposterior\b|\bMCMC\b")


def main():
    report = "--report" in sys.argv
    load_nouns()
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

    def name_words(n):
        # `flatLCDM_fits_pantheon_SN` -> "flat LCDM fits pantheon SN"
        return " ".join(re.findall(r"[A-Z]+(?![a-z])|[A-Z]?[a-z]+|\d+", n.replace("Checked.", "", 1)))

    for h in heads.values():
        doc = h["doc"]
        vocab(h["name"], doc, h["pinned"] + h.get("laws", []))
        # rule 8 (run 2026-11-05T1428Z; blind red team K, d05: a headline proving only that a flat ΛCDM
        # scale factor EXISTS was named `flatLCDM_fits_pantheon_SN` in a module `PantheonFlatLCDM` with the
        # docstring "the value that fits the Pantheon supernovae"; no check read names, and no rule tied
        # data words to data): (a) the glossary applies to the headline's name and module name too;
        # (b) data words (fit, data, supernova, χ², likelihood, survey names, ...) in its docstring, name or
        # module name need a statement that reaches a PRINTED definition (a transcribed table or source)
        nm = name_words(h["name"] + " " + h.get("module", ""))
        own = name_words(h["name"])
        for rx, c, backs in gloss:
            m = c.search(own)
            if m and not (backs & {short(p) for p in h["pinned"] + h.get("laws", [])}):
                errs.append((f"{h['name']}|name-vocab|{rx}", f"{h['name']}: its name says '{m.group(0)}' but the statement "
                            f"reaches none of the pinned definitions {sorted(backs)} that give that term its meaning"))
        kinds_h = set(h.get("defs", {}).values())
        for where, text in (("docstring", strip_code_names(doc)), ("name or module", nm)):
            m = DATA.search(text)
            if m and "PRINTED" not in kinds_h:
                errs.append((f"{h['name']}|data|{where}", f"{h['name']}: its {where} says '{m.group(0)}' (a claim about data or a "
                            f"fit) but the statement reaches no PRINTED definition (no transcribed table or source): a data "
                            f"claim needs the data in the statement"))
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
        if "nums" in h:
            signed = {Fraction(x) for x in h["nums"]}
            have = {abs(v) for v in signed}
            text_n = strip_citations(strip_code_names(doc), h["name"])
            for m in NUM.finditer(text_n):
                v = num_value(m.group(2))
                # an explicit sign in the prose is compared signed (adversary: |·| hid sign errors);
                # an unsigned number may match a literal of either sign (the statement may write -x)
                ok = (-v in signed) if m.group(1) else (v in have)
                # an unsigned number that matches only a NEGATIVE literal must say so in words (red team H,
                # d05, run 2026-11-04T1428Z: "the acentric factor is 0.3020" on a statement certifying −0.3020)
                if ok and not m.group(1) and v not in signed and v != 0:
                    before = text_n[max(0, m.start() - 30):m.start()]
                    if not re.search(r"(?i)minus|negative|below zero|[−-]\s*$", before):
                        errs.append((f"{h['name']}|number-sign|{m.group(2)}", f"{h['name']}: its docstring names {m.group(2)} "
                                     f"without a sign, but the statement certifies only −{m.group(2)} (write the sign, or 'minus'/'negative')"))
                if not ok:
                    tok = m.group(1) + m.group(2)
                    errs.append((f"{h['name']}|number|{tok}", f"{h['name']}: its docstring names the number "
                                 f"{tok}, which is not a numeric literal of its statement (a derived number belongs in a "
                                 f"registered record that certifies it; a citation is written `(N.M)` or `Eq. N.M`)"))
        if "bound" in h:
            param_rule(h, errs)
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
    # rule 7 (run 2026-11-04T1428Z; red team H, d06: the `/-! -/` doc of a NEW module claimed a 0.45 mag
    # margin next to an honest headline certifying 3/10): every decimal or fraction in the module doc of a
    # Checked file is a numeric literal of a headline stated in that file, or a registered citation of one
    # of them; old module-doc numbers are baselined per number (`<module>|moduledoc|<number>`)
    decl = re.compile(r"(?m)^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+)?(?:theorem|lemma)\s+([^\s:(]+)")
    for f in sorted((ROOT / "Checked").rglob("*.lean")):
        src = f.read_text(encoding="utf-8")
        docs = re.findall(r"/-!(.*?)-/", src, re.S)
        if not docs:
            continue
        mod = "Checked." + ".".join(f.relative_to(ROOT / "Checked").with_suffix("").parts)
        names = set(decl.findall(src))
        local = [h for h in heads.values() if short(h["name"]) in names]
        signed = {Fraction(x) for h in local for x in h.get("nums", [])}
        have = {abs(v) for v in signed}
        cited = {n for o, n in oreg_all() if o in {h["name"] for h in local}}
        text = strip_code_names("\n".join(docs))
        text = CITE.sub(lambda m: m.group(0) if not all(n in cited for n in re.findall(r"[1-9]\d?\.\d{1,2}", m.group(0)))
                        else " " * len(m.group(0)), text)
        for m in NUM.finditer(text):
            v = num_value(m.group(2))
            ok = (-v in signed) if m.group(1) else (v in have)
            if not ok:
                tok = m.group(1) + m.group(2)
                errs.append((f"{mod}|moduledoc|{tok}", f"{mod}: its module doc names the number {tok}, which is not a numeric "
                             f"literal of a headline stated in this file (certify it in a registered record, or cite it as `(N.M)`)"))
    cpath = ROOT / "scripts/trust/citations.txt"
    creg = {l.strip() for l in cpath.read_text().splitlines() if l.strip() and not l.startswith("#")} if cpath.exists() else set()
    if "--write-citations" in sys.argv:
        cpath.write_text("# Equation numbers that headline docstrings may cite as `(N.M)` / `Eq. N.M` (check_prose rule 5).\n"
                         "# Generated at run 2026-11-04T1028Z from the headline docstrings and FINDINGS.md on main; may grow only with a LEDGER.md\n"
                         "# addition naming the new number (--base). A number written as a citation is not read as a value.\n"
                         + "".join(n + "\n" for n in sorted(creg | {n for _, n in CITED}, key=lambda x: tuple(map(int, x.split("."))))))
        print(f"citations written: {len({n for _, n in CITED})}")
        return
    # citations are registered per headline (red team H, d08, run 2026-11-04T1428Z: a NEW headline wrote a
    # value as "(1.9)", a number registered because another docstring cites Eq. (1.9)): a headline may cite
    # (N.M) only if `<headline> N.M` is in citation_owners.txt; growth needs a LEDGER.md addition naming both
    opath = ROOT / "scripts/trust/citation_owners.txt"
    if "--write-citation-owners" in sys.argv:
        opath.write_text("# Per-headline citations (check_prose rule 5, run 2026-11-04T1428Z): `<headline> <N.M>`. A headline docstring\n"
                         "# may cite (N.M) only if its line is here. Generated from main at d714f04; may grow only with a LEDGER.md\n"
                         "# addition naming the headline's short name and the number (--base).\n"
                         + "".join(f"{o} {n}\n" for o, n in sorted(set(CITED))), encoding="utf-8")
        print(f"citation owners written: {len(set(CITED))}")
        return
    oreg = {tuple(l.split()) for l in opath.read_text(encoding="utf-8").splitlines() if l.strip() and not l.startswith("#")} if opath.exists() else set()
    for owner, n in CITED:
        if opath.exists() and owner in heads and (owner, n) not in oreg:
            errs.append((f"{owner}|citation-owner|{n}", f"{owner}: its docstring cites ({n}), registered for other headlines but not for "
                         f"this one (scripts/trust/citation_owners.txt): a value written as a citation is not read by the number rule"))
        if n not in creg:
            errs.append((f"{owner}|citation|{n}", f"{owner}: its docstring cites ({n}), which is not a registered equation number "
                         f"(scripts/trust/citations.txt): a value written as a citation is not read by the number rule"))
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
        oo = old("scripts/trust/citation_owners.txt")
        if oo is not None:
            oold = {tuple(l.split()) for l in oo.splitlines() if l.strip() and not l.startswith("#")}
            ogrown = oreg - oold
            if ogrown:
                r = subprocess.run(["git", "diff", b, "HEAD", "--", "LEDGER.md"], cwd=ROOT, capture_output=True, text=True)
                added = "\n".join(l for l in r.stdout.splitlines() if l.startswith("+"))
                undisclosed = sorted(f"{o} {n}" for o, n in ogrown if not (short(o) in added and n in added))
                if undisclosed:
                    print(f"citation_owners.txt grew against {b} without a LEDGER.md addition naming: {undisclosed}")
                    fail = True
        oc = old("scripts/trust/citations.txt")
        if oc is not None:
            cgrown = creg - {l.strip() for l in oc.splitlines() if l.strip() and not l.startswith("#")}
            if cgrown:
                r = subprocess.run(["git", "diff", b, "HEAD", "--", "LEDGER.md"], cwd=ROOT, capture_output=True, text=True)
                added = "\n".join(l for l in r.stdout.splitlines() if l.startswith("+"))
                undisclosed = sorted(n for n in cgrown if n not in added)
                if undisclosed:
                    print(f"citations.txt grew against {b} without a LEDGER.md addition naming: {undisclosed}")
                    fail = True
        on = old("scripts/trust/param_nouns.txt")
        if on is not None:
            nnow = (ROOT / "scripts/trust/param_nouns.txt").read_text(encoding="utf-8").splitlines()
            olds = [l for l in on.splitlines() if l and not l.startswith("#")]
            lost = [l for l in olds if l not in nnow]
            if lost:
                print(f"param_nouns.txt lost or changed entries against {b}: {lost} (the noun registry may only grow)")
                fail = True
            added_n = [l for l in nnow if l and not l.startswith("#") and l not in olds]
            if added_n:
                r = subprocess.run(["git", "diff", b, "HEAD", "--", "LEDGER.md"], cwd=ROOT, capture_output=True, text=True)
                ladd = "\n".join(l for l in r.stdout.splitlines() if l.startswith("+"))
                undisclosed = [l for l in added_n if l.split(" => ")[0] not in ladd]
                if undisclosed:
                    print(f"param_nouns.txt grew against {b} without a LEDGER.md addition naming the noun regex: {undisclosed}")
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
