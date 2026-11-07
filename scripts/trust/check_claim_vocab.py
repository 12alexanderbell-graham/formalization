#!/usr/bin/env python3
"""Headline paraphrases use the claim's own words (run 2026-11-06T2228Z, part 3; written AFTER reading blind red
team P's report — not blind). Blocking in CI after CLAIMS.md is regenerated; reads CLAIMS.md only (no Lean).

Why (rounds F, G, J, N, O, P): every round put the false part of a claim into the author's paraphrase of a true
headline, and every vocabulary DENY-list (inference connectives, generality, persistence, two-sided and grading
words) was routed around by the next round with a word it did not list: P d01 "The peak implies that the problem
has exactly one solution", d02 "bounded by this value for the full duration of the run", d04 "reproduces the
critical parameter 3.321992118 to within 10⁻¹²" over a one-sided bound, d05 "an inverted potential has a
vanishing natural frequency" over a junk value √(negative) = 0. This check inverts the list: a paraphrase may
only use words that the GENERATED claim (CLAIMS.md: statement, connectives, pinned phrases, definition bodies)
already uses, plus a fixed list of function words below, plus a disclosed domain vocabulary. A paraphrase can
then rephrase and name things, but every new concept word is visible in one registry, reviewed when added.

  python3 scripts/trust/check_claim_vocab.py              V1-V2 on the current tree
  python3 scripts/trust/check_claim_vocab.py --base SHA   also V3-V4 (baseline shrink-only; vocabulary growth disclosed)
  python3 scripts/trust/check_claim_vocab.py --report     print every finding, never fail

V1 (closed vocabulary): every word of a headline's paraphrase in CLAIMS.md (code spans, citations and single
   letters removed; possessive 's and a plural s/es ignored) occurs in the generated part of the same CLAIMS.md
   section, in FUNCTION below, or in `scripts/trust/prose_vocab.txt`.
V2 (the vocabulary carries no claim): no entry of prose_vocab.txt is an inference, generality, persistence,
   two-sided, grading or strength word (the deny-lists of check_claim_words, check_prose_gen, check_prose_eval
   and STRENGTH below) — those words reach a paraphrase only when the generated claim itself uses them.
V3 (--base): `scripts/trust/claim_vocab_baseline.txt` (keys `<full name>|<word>` and `<full name>|num:<number>`,
   populated from the tree when the rule was written) may only shrink, except in a commit that changes this script
   and adds a LEDGER line mentioning the baseline file (a stricter rule regenerates it).
V6 (numbers): every numeral of a paraphrase (digits, decimals, superscript powers) is a numeral of the generated
   claim.
V5 (junk values): no conclusion of a generated claim (its "then"/"It holds that" part) equates a square root or a
   logarithm to 0 or divides by the literal 0, divides by (inverts, logs, roots) a variable a hypothesis sets to 0,
   or uses `deriv` when the claim nowhere asserts differentiability (the last two since Q d02, d03): Mathlib's √x = 0 for x < 0, log 0 = 0 and x / 0 = 0 are
   conventions, and a headline about them certifies the convention, not mathematics (P d05: `√(k / m) = 0` for
   k < 0, "an inverted potential has a vanishing natural frequency"). CLAIMS.md's notation block states the
   conventions since this run.
V4 (--base): each word added to prose_vocab.txt is named in backticks on a LEDGER.md line added since the base
   that mentions prose_vocab.txt.

Limits: a misleading paraphrase built only from the claim's own words and the disclosed vocabulary (word order,
negation of a generated phrase, a vocabulary word used in a stronger sense than its review); prose outside
CLAIMS.md paraphrases (Work docstrings, STATE.md beyond check_status_lines.py, run records).
"""
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_claim_words as W  # noqa: E402
import check_prose_gen as G  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]
BASELINE = "scripts/trust/claim_vocab_baseline.txt"
VOCAB = "scripts/trust/prose_vocab.txt"

# function words and neutral mathematical vocabulary (no quantity, no strength, no domain); frozen in this file
FUNCTION = set("""
a an the of to in on at for from by with and or as is are be been being was were has have had its it itself
their they them this that these those which whose where when what than then if such some one two three four five
six seven eight nine ten first second third fourth fifth sixth both each not no nor also into onto over under
below above between within out up down per via while whereas but same other another own here there
value values number numbers function functions solution solutions equation equations interval intervals point
points parameter parameters variable variables real positive negative nonnegative nonpositive nonzero zero
derivative derivatives continuous differentiable polynomial polynomials coefficient coefficients bound bounds
lower upper lies lie equals equal satisfies satisfy satisfying satisfied obeying obeys meeting meets holds hold
given strictly least most sum product square root roots ratio term terms order series limit integral decimal
decimals place places rounds rounded left right side sides end ends expression expressions formula formulas
identity identities condition conditions hypothesis hypotheses statement case cases defined definition
more less larger smaller greater exceeds exceed times see
""".split())

# claim-strength words that may not enter the domain vocabulary (V2): they change what is claimed
STRENGTH = re.compile(r"(?i)^(?:unique|uniquely|uniqueness|exactly|only|sole|solely|necessarily|necessary|sufficient|"
                      r"sufficiently|implies|implied|imply|entails?|guarantees?|guaranteed|ensures?|proves?|proven|"
                      r"certif\w*|verif\w*|rigorous\w*|exact|exactness|precise\w*|accura\w*|correct\w*|true|false|"
                      r"full|fully|entire|entirely|whole|complete\w*|total|totally|never|forever|permanent\w*|"
                      r"stable|stability|unstable|instability|duration|lifetime|throughout|everywhere|always|"
                      r"all|every|any|each|whenever|wherever|general|generally|universal\w*|global\w*|"
                      # long-time behaviour (since Q d05 "the system has settled at equilibrium" over exp(−t) < 1/2)
                      r"settle\w*|converg\w*|asymptot\w*|final|finally|eventual\w*|ultimate\w*)$")

WORD = re.compile(r"[A-Za-zÀ-ÖØ-öø-ÿ]+(?:['’][A-Za-z]+)?")


def norm(w):
    w = w.lower().replace("’", "'")
    if w.endswith("'s"):
        w = w[:-2]
    return w


def forms(w):
    out = {w}
    if w.endswith("es"):
        out.add(w[:-2])
    if w.endswith("s"):
        out.add(w[:-1])
    if w.endswith("ies"):
        out.add(w[:-3] + "y")
    return out


def words(text):
    text = re.sub(r"`[^`]*`", " ", text)
    text = re.sub(r"\[[^\]]*\]", " ", text)  # certified-number tags and citations
    return [norm(w) for w in WORD.findall(text)]


def sections(path=None):
    """(full name, generated text, paraphrase text) per headline section of CLAIMS.md"""
    txt = (path or ROOT / "CLAIMS.md").read_text(encoding="utf-8")
    out = []
    for s in re.split(r"\n## `", txt)[1:]:
        lines = s.split("\n")
        full = None
        m = re.search(r"Full name `([^`]+)`", s)
        if m:
            full = m.group(1)
        para, gen = [], []
        for l in lines:
            if l.startswith("> ") or l == ">":
                para.append(l[2:])
            elif not l.startswith("Author's paraphrase"):
                gen.append(l)
        out.append((full or lines[0].split("`")[0], "\n".join(gen), " ".join(para)))
    return out


SUP = str.maketrans("⁰¹²³⁴⁵⁶⁷⁸⁹⁻", "0123456789-")


def author_names(gen):
    """the identifiers the author chose freely: the headline's own name (heading and Full name line) and the
    names of its bound variables (`x : T` in the generated text). Since run 2026-11-06T2228Z (blind red team Q,
    d02 `acceleration_of_zero_mass` with binders `force`, `mass`; d04 `energy_below_some_level`) they are not
    claim words: a name is the author's prose, not something the statement establishes."""
    names = set()
    lines = gen.split("\n")
    for l in lines[:1] + [l for l in lines if l.startswith("Full name")]:
        for ident in re.findall(r"[A-Za-z][A-Za-z0-9_'.]*", l.split("`")[1] if "`" in l else l):
            names.update(ident.split("."))
    for span in re.findall(r"`([^`]*)`", gen):
        names.update(m.group(1) for m in re.finditer(r"(?:^|[(\s])([A-Za-z][A-Za-z0-9_']*)\s*:\s", span))
    return names


def split_ident(ident):
    ident = re.sub(r"([a-z])([A-Z])", r"\1 \2", ident)
    return {norm(p) for p in re.split(r"[_\s.\d']+", ident) if p}


def gen_vocab(gen):
    lines = gen.split("\n")
    body = "\n".join(l for i, l in enumerate(lines) if i > 0 and not l.startswith("Full name"))
    own = author_names(gen)
    v = set(words(re.sub(r"`[^`]*`", " ", body)))
    # identifiers inside code spans contribute their words too (camelCase / snake_case parts), except the
    # headline's own name and its binder names
    for span in re.findall(r"`([^`]*)`", body):
        for ident in re.findall(r"[A-Za-z][A-Za-z0-9_']*", span):
            if ident not in own:
                v |= split_ident(ident)
    return v


def numbers(text):
    """numerals of a text as {string: value}; a superscript run is an exponent (10⁴ → 10^4 → 10000, judge P AFTER);
    `a ^ b` and `aeb` also contribute their value"""
    from fractions import Fraction
    text = re.sub(r"[⁻⁰¹²³⁴⁵⁶⁷⁸⁹]+", lambda m: "^" + m.group(0).translate(SUP), text).replace("−", "-")
    out = {}
    for m in re.finditer(r"(?:(?<![\w.^])-)?\d+(?:\.\d+)?", text):
        out[m.group(0)] = Fraction(m.group(0))
    for m in re.finditer(r"(\d+(?:\.\d+)?)\s*\^\s*\(?\s*(-?\d+)", text):
        out[m.group(0).replace(" ", "")] = Fraction(m.group(1)) ** int(m.group(2))
    for m in re.finditer(r"(\d+(?:\.\d+)?)\s*[·×*]\s*10\s*\^\s*\(?\s*(-?\d+)", text):
        out[m.group(0).replace(" ", "")] = Fraction(m.group(1)) * Fraction(10) ** int(m.group(2))
    for m in re.finditer(r"(\d+(?:\.\d+)?)e(-?\d+)", text):
        out[m.group(0)] = Fraction(m.group(1)) * Fraction(10) ** int(m.group(2))
    return out


def gen_numbers(gen):
    lines = gen.split("\n")
    body = "\n".join(l for i, l in enumerate(lines) if i > 0 and not l.startswith("Full name"))
    return {abs(v) for v in numbers(body).values()}


def load_set(rel, text=None):
    if text is None:
        p = ROOT / rel
        text = p.read_text(encoding="utf-8") if p.exists() else ""
    return {l.split("#")[0].strip().lower() for l in text.splitlines() if l.split("#")[0].strip()}


def findings(vocab):
    out = []
    for full, gen, para in sections():
        out += junk(full, gen)
        if not para.strip():
            continue
        gv = gen_vocab(gen)
        seen = set()
        for w in words(para):
            if len(w) == 1 or w in seen:
                continue
            seen.add(w)
            f = forms(w)
            if f & gv or f & FUNCTION or f & vocab:
                continue
            out.append((f"{full}|{w}", f"V1: {full}: its paraphrase says '{w}', a word the generated claim does not use "
                        f"(add it to {VOCAB} with a LEDGER line if it names something, or say what the statement proves)"))
        # V6 (run 2026-11-06T2228Z, blind red team Q d06: "equals 2.718 to 6 decimal places" over `RoundsTo … 2.718 3`):
        # every numeral of the paraphrase is a numeral of the generated claim
        gn = gen_numbers(gen)
        para_n = re.sub(r"`[^`]*`", " ", para)
        para_n = re.sub(r"\[[^\]]*\]", " ", para_n)
        para_n = W.C.CITE.sub(" ", para_n)  # equation citations `(N.M)`, `Eq. N.M` (check_prose registers them)
        para_n = re.sub(r"\b(?:19|20)\d\d(?:-\d\d(?:-\d\d)?)?(?:T\d{4}Z)?\b", " ", para_n)  # years and dates (check_prose rule 9 reads sources)
        pn = numbers(para_n)
        # an exponent's base and exponent alone are not read when the power itself is a claim value
        powers = [k for k in pn if "^" in k and abs(pn[k]) in gn]
        skip = {x for k in powers for x in re.findall(r"-?\d+(?:\.\d+)?", k)}
        skip |= {k2 for k in powers for k2 in pn if "^" in k2 and k2 in k}
        for n in sorted(pn):
            if abs(pn[n]) not in gn and not (n in skip or n.lstrip("-") in skip):
                out.append((f"{full}|num:{n}", f"V6: {full}: its paraphrase names the number {n}, which the generated claim "
                            f"does not contain (a number a reader takes from the paraphrase must be the statement's)"))
    return out


JUNK = re.compile(r"(?:√|Real\.sqrt|Real\.logb?\b)[^=≠]*=\s*0(?![.\d])|=\s*0\s*$.*|/\s*0(?![.\d])")


def junk(full, gen):
    m = re.search(r"\*\*(?:then|It holds that)\*\*(.*?)(?:\nProgram definitions|$)", gen, re.S)
    if not m:
        return []
    out = []
    for span in re.findall(r"`([^`]*)`", m.group(1)):
        if re.search(r"√|Real\.sqrt|Real\.logb?\b", span) and re.search(r"=\s*0(?![.\d])", span) or re.search(r"/\s*0(?![.\d])", span):
            out.append((f"{full}|junk", f"V5: {full}: its conclusion `{span[:80]}` equates a square root or logarithm to 0 "
                        f"or divides by 0 (Mathlib junk-value conventions): a headline may not certify a convention"))
    # (run 2026-11-06T2228Z, blind red team Q d03: `deriv (fun x => |x|) 0 = 0`, Mathlib's derivative where none
    # exists) a conclusion about `deriv`/`iteratedDeriv` needs differentiability somewhere in the claim
    concl = " ".join(re.findall(r"`([^`]*)`", m.group(1)))
    if re.search(r"\b(?:deriv|iteratedDeriv|derivWithin|fderiv)\b", concl) and not re.search(
            r"HasDerivAt|HasDerivWithinAt|HasFDerivAt|Differentiable|ContDiff|HasStrictDerivAt", gen):
        out.append((f"{full}|junk-deriv", f"V5: {full}: its conclusion uses a derivative (`deriv`) but the claim nowhere "
                    f"asserts differentiability: Mathlib's derivative is 0 where none exists"))
    # (Q d02: `force / mass = 0` under `mass = 0`) a variable a hypothesis sets to 0 is not divided by, inverted,
    # logged or square-rooted in the conclusion
    hyp = re.search(r"\*\*assuming\*\*(.*?)\*\*then\*\*", gen, re.S)
    zero = set()
    if hyp:
        for span in re.findall(r"`([^`]*)`", hyp.group(1)):
            z = re.fullmatch(r"\s*([A-Za-z_][A-Za-z0-9_']*)\s*=\s*0\s*|\s*0\s*=\s*([A-Za-z_][A-Za-z0-9_']*)\s*", span)
            if z:
                zero.add(z.group(1) or z.group(2))
    for v in sorted(zero):
        if re.search(r"/\s*\(?\s*" + re.escape(v) + r"\b|\b" + re.escape(v) + r"\s*⁻¹|(?:Real\.logb?|√|Real\.sqrt)\s*\(?\s*"
                     + re.escape(v) + r"\b", concl):
            out.append((f"{full}|junk-zero|{v}", f"V5: {full}: a hypothesis sets {v} = 0 and the conclusion divides by, "
                        f"inverts, logs or square-roots {v}: Mathlib's x/0 = 0 is a convention"))
    return out[:3]


def deny(w):
    return (STRENGTH.match(w) or W.INFER.fullmatch(w) or W.GRADE.fullmatch(w) or W.PERSIST.fullmatch(w)
            or W.TWO_SIDED.fullmatch(w) or W.NAME_EXTRA_DOMAIN.fullmatch(w) or W.NAME_EXTRA_CASES.fullmatch(w)
            or G.WORDS.fullmatch(w))


def git(*args):
    r = subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else None


def main():
    base = sys.argv[sys.argv.index("--base") + 1] if "--base" in sys.argv else None
    report = "--report" in sys.argv
    vocab = load_set(VOCAB)
    found = findings(vocab)
    keys = {k for k, _ in found}
    if report:
        for k, m in found:
            print(m)
        print(f"check_claim_vocab: {len(found)} findings (report only)")
        return 0
    bl = load_set(BASELINE)
    errors = [m for k, m in found if k.lower() not in bl]
    errors += [f"{BASELINE}: {k} no longer fires; remove the line (shrink-only)" for k in sorted(bl - {k.lower() for k in keys})]
    errors += [f"V2: {VOCAB}: '{w}' is an inference, generality, persistence, two-sided, grading or strength word; it may "
               f"reach a paraphrase only through the generated claim" for w in sorted(vocab) if deny(w)]
    if base:
        old = git("show", f"{base}:{BASELINE}")
        if old is not None:
            grown = sorted(bl - load_set(BASELINE, old))
            # growth only when this script itself changed (a stricter rule regenerates the baseline) and an added
            # LEDGER line mentions the baseline file
            ledger_added = [l for l in (git("diff", base, "--", "LEDGER.md") or "").splitlines()
                            if l.startswith("+") and "claim_vocab_baseline" in l]
            if grown and not (git("diff", "--quiet", base, "--", "scripts/trust/check_claim_vocab.py") is None and ledger_added):
                errors += [f"V3: {BASELINE} grew against {base}: {k} (it may only shrink)" for k in grown]
        oldv = git("show", f"{base}:{VOCAB}")
        added = sorted(vocab - (load_set(VOCAB, oldv) if oldv is not None else set()))
        if added:
            diff = git("diff", base, "--", "LEDGER.md") or ""
            lines = [l[1:] for l in diff.splitlines() if l.startswith("+") and not l.startswith("+++") and "prose_vocab" in l]
            named = {norm(x) for l in lines for x in re.findall(r"`([^`]+)`", l)}
            errors += [f"V4: {VOCAB}: '{w}' added without a LEDGER.md line (mentioning prose_vocab.txt) that names it "
                       f"in backticks" for w in added if w not in named]
    for e in errors:
        print("  " + e)
    print(f"check_claim_vocab: {len(sections())} sections, {len(found)} findings ({len(bl & {k.lower() for k in keys})} "
          f"baselined), vocabulary {len(vocab)}; {'FAIL' if errors else 'ok'}")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
