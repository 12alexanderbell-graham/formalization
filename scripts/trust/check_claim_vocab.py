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
V7 (quantifier order; run 2026-11-07T0028Z, after blind red team Q d04 — not blind): the sequence of quantifier
   phrases of a paraphrase (universal: every/all/any/each/whenever, existential: there is/are/exists, exist(s), some;
   adjacent phrases of one kind merged; code spans removed; "there is no" not counted) must be a subsequence of the
   same sequence read from the generated claim (its statement part, then the program definitions it lists). Q d04 wrote ∀E ∃n as
   "there is a level n such that … for every E" with the claim's own words: E-then-U is not a subsequence of U-then-E.
   Postpositive universals ("models exist for every Ω") are rejected too: say "for every Ω there is …".
   Limits: nesting beyond the order (which existential an "every" sits under), quantifiers expressed without these
   words ("a level above each energy" counts; "a level above the energies" does not).
V8 (names; run 2026-11-07T0028Z, after blind red team R d02 — not blind): a STRENGTH word in the headline's name
   (unique, exact, sharp, optimal, …) must occur in its generated claim.
V11 (quoted relations; run 2026-11-07T1428Z, after reading blind red team S — not blind): a paraphrase code span
   that states a relation must occur verbatim (whitespace ignored) in the generated claim. Also since S: V10 reads
   BIND words within three words of a numeral and numerals glued to D ("3D"); STRENGTH (so V2 and V8) includes
   arbitrary/generic/independent/regardless/irrespective.
V10 (bound numerals; run 2026-11-07T1428Z, after judging blind red team R d04 — not blind): a numeral next to a
   disclosed-vocabulary word ("dimension 2", "two-dimensional") needs that word's Lean shape with that numeral in the
   generated claim (`BIND`: `Fin n` for dimension, `ContDiff ℝ n` for "n times continuously"); V6 now also reads
   numerals inside code spans and the number words two…ten.
V9 (unpinned names; run 2026-11-07T1428Z, after judging blind red team R d03 — not blind): identifiers of program
   definitions the section lists as not pinned contribute no words to the generated vocabulary of V1/V8: CLAIMS.md
   says only their formula is checked, not their name (R d03: COMPOSITE `IsDecelerating a t := decel a t < 0`, true
   of de Sitter, paraphrased "is decelerating").
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
                      r"settle\w*|converg\w*|asymptot\w*|final|finally|eventual\w*|ultimate\w*|"
                      # optimality (since R d06 "and this bound is sharp" over `lam ≤ 4`, `sharp` disclosed)
                      r"sharp\w*|tight\w*|optimal\w*|optimum|best|improv\w*|unimprov\w*|attain\w*|achiev\w*|"
                      # arbitrary data (since S d03 `rob_state40_arbitrary_rates` over fixed rate constants; not blind)
                      r"arbitrar\w*|generic\w*|independen\w*|regardless|irrespective\w*)$")

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


def unpinned_names(gen):
    """V9 (run 2026-11-07T1428Z, after judging blind red team R d03 on main — not blind): the names of the program
    definitions the section lists as not pinned (`- `Name args` — KIND, not pinned …`). CLAIMS.md itself says that
    only such a definition's formula is checked, not its name, so its name is the author's prose like the
    headline's own name and binders (R d03: COMPOSITE `IsDecelerating a t := decel a t < 0`, true of de Sitter,
    paraphrased "the scale factor is decelerating": 'decelerating' came only from the unpinned name)."""
    names = set()
    for m in re.finditer(r"(?m)^- `([A-Za-z_][A-Za-z0-9_'.]*)[^`]*` — (?!\*\*PINNED)", gen):
        names.add(m.group(1))
        names.add(m.group(1).split(".")[-1])
    return names


def gen_vocab(gen):
    lines = gen.split("\n")
    body = "\n".join(l for i, l in enumerate(lines) if i > 0 and not l.startswith("Full name"))
    own = author_names(gen) | unpinned_names(gen)
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
    claims_seen = {}
    for full, gen, para in sections():
        out += junk(full, gen)
        out += name_strength(full, gen)
        out += name_vocab(full, gen, vocab)
        out += duplicate(full, gen, claims_seen)
        if not para.strip():
            continue
        out += order(full, gen, para)
        out += bound_numerals(full, gen, para, vocab)
        out += numeral_context(full, gen, para)
        out += quoted_spans(full, gen, para)
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
        # since run 2026-11-07T1428Z (not blind, R d04 judged): numerals inside the paraphrase's code spans and the
        # cardinal number words two…ten are read too (before, "dimension `2`" or "two-dimensional" escaped V6)
        para_n = re.sub(r"`([^`]*)`", lambda m: " " + m.group(1) + " ", para)
        para_n = re.sub(r"(?i)\b(" + "|".join(k for k in NUMWORD if k != "twice") + r")\b",
                        lambda m: " " + str(NUMWORD[m.group(1).lower()]) + " ", para_n)
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


NUMWORD = {"two": 2, "three": 3, "four": 4, "five": 5, "six": 6, "seven": 7, "eight": 8, "nine": 9, "ten": 10,
           "twice": 2}
NUMTOK = r"(?:\d+(?:\.\d+)?|" + "|".join(NUMWORD) + r")"
# V10 bindings: a numeral attached to one of these vocabulary words is licensed only if the generated claim contains
# the numeral in the named Lean shape (the word's meaning, written as the statement must say it)
BIND = [
    (re.compile(r"(?i)^(?:dimension|dimensional|dimensions|d)$"), lambda n: rf"\bFin\s+{n}\b"),
    (re.compile(r"(?i)^(?:continuously|differentiable|times)$"), lambda n: rf"\bContDiff(?:On|At|WithinAt)?\s+ℝ\s+{n}\b"),
]


def quoted_spans(full, gen, para):
    """V11 (run 2026-11-07T1428Z, after reading blind red team S d05 — not blind): a code span of a paraphrase that
    states a relation (<, ≤, =, ≥, >, ∈) is a quotation of the statement: it must occur in the generated claim
    (whitespace ignored). S d05 swapped the bounds of y₁ and y₃ inside code spans built from the claim's own
    numerals and names; V6 compares numerals as a set. Older paraphrases' informal formulas are baselined."""
    g = re.sub(r"\s+", "", gen)
    out = []
    for sp in re.findall(r"`([^`]*)`", para):
        # V12 (run 2026-11-07T1828Z, after reading blind red team T d03 — not blind): a span that states no relation
        # but is a formula (anything but one identifier or one numeral) is a quotation too. T d03 wrote the Townes
        # equation's right-hand side `-(1 / r * φ r) + θ r + θ r ^ 3` with the sign of θ³ flipped (the claim has
        # `- θ r ^ 3`): no relation symbol, so V11 did not read it, and V6 compares numerals as a set.
        if (not re.search(r"[<≤=≥>∈]", sp) and not re.fullmatch(r"\s*[\w.'′₀-₉⁰-⁹]+\s*", sp)
                and re.sub(r"\s+", "", sp) not in g):
            out.append((f"{full}|fspan:{re.sub(r'[|#]', ' ', sp.strip())[:80]}",
                        f"V12: {full}: its paraphrase writes `{sp.strip()[:80]}` as code, a formula that does not occur "
                        f"in the generated claim (a code span is read as a quotation of the statement: quote it exactly "
                        f"or write it as prose)"))
            continue
        if re.search(r"[<≤=≥>∈]", sp) and re.sub(r"\s+", "", sp) not in g:
            out.append((f"{full}|span:{re.sub(r'[|#]', ' ', sp.strip())[:80]}",
                        f"V11: {full}: its paraphrase writes `{sp.strip()[:80]}` as code, a relation that does not occur in "
                        f"the generated claim: quote the statement or say it in words"))
    return out


def numval(t):
    t = t.lower()
    return str(NUMWORD[t]) if t in NUMWORD else t


def bound_numerals(full, gen, para, vocab):
    """V10 (run 2026-11-07T1428Z, after judging blind red team R d04 on main — not blind): a numeral (digits or a
    number word two…ten, twice) written next to a word of the disclosed vocabulary (`dimension 2`, `two-dimensional`,
    `twice continuously`) — a word the generated claim does not use — states what the number counts. V6 compared
    numerals as a set: R d04 wrote "In dimension 2" over a statement on `EuclideanSpace ℝ (Fin 3)` whose 2 is the
    differentiability order. Such a numeral is licensed only by BIND (the word's Lean shape with that numeral occurs
    in the generated claim, e.g. `Fin 3` for "three-dimensional"); otherwise the finding fires (baseline for older
    paraphrases)."""
    gv = gen_vocab(gen)
    text = re.sub(r"`[^`]*`", " ", para)
    # a numeral glued to a dimension letter ("3D", "2-D", "3d") is a dimension (since S d02 "in 3D"; not blind)
    text = re.sub(r"(?i)\b(\d+)[\s-]?d\b", r"\1 dimensional", text)
    out = []
    pairs = []
    for m in re.finditer(rf"(?i)\b({NUMTOK})[\s-]+([A-Za-z]+)|\b([A-Za-z]+)[\s-]+({NUMTOK})\b", text):
        num, w = (m.group(1), m.group(2)) if m.group(1) else (m.group(4), m.group(3))
        pairs.append((num, w))
    # BIND families are read in a window of three words on each side of a numeral, whether or not the word is in
    # the disclosed vocabulary (since S d01 "three times continuously differentiable": the word next to the
    # numeral was 'times', not a vocabulary word; not blind)
    toks = re.findall(rf"(?i){NUMTOK}|[A-Za-z]+", text)
    for i, t in enumerate(toks):
        if not re.fullmatch(rf"(?i){NUMTOK}", t):
            continue
        near = toks[max(0, i - 2):i] + toks[i + 1:i + 3]
        for w in near:
            if BIND[0][0].match(w) and (t, w) not in pairs:
                pairs.append((t, w))
        # "n times … differentiable / continuously" (and "twice …"): the count of derivatives
        after = toks[i + 1:i + 5]
        if (t.lower() == "twice" or (after[:1] and after[0].lower() == "times")) and any(
                re.fullmatch(r"(?i)differentiable|continuously|smooth", w) for w in after):
            pairs.append((t, "times"))
    for num, w in pairs:
        f = forms(norm(w))
        bound = [shape for rx, shape in BIND if rx.match(w)]
        if not bound and (not (f & vocab) or (f & gv)):
            continue
        n = numval(num)
        if bound and any(re.search(shape(n), gen) for shape in bound):
            continue
        if not bound and any(rx.match(w) and re.search(shape(n), gen) for rx, shape in BIND):
            continue
        out.append((f"{full}|bind:{norm(w)}:{n}", f"V10: {full}: its paraphrase attaches the number {num} to '{w}', a "
                    f"vocabulary word the generated claim does not use, and the claim does not state that number in "
                    f"that role (a disclosed word may name things, not count them)"))
    return out



def name_vocab(full, gen, vocab):
    """V13 (run 2026-11-07T1828Z, after reading blind red team T d06 — not blind): every word of a headline's name
    (all components after `Checked.<Area>.`, camelCase and snake_case split) is a word of its generated claim, a
    FUNCTION word or a disclosed vocabulary word (prose_vocab.txt, which V2 keeps free of strength and inference
    words) — the allow-list V1 applies to paraphrases, applied to names. V8 read names against a deny-list (STRENGTH)
    and was routed around within one round: T d06 registered the one-sided bound `lam ≤ 3.321992119` (for every
    radial solution) as `GelfandPDEThreshold.gelfand_pde_radial_solvability_threshold`, a name that promises the
    two-sided statement. 'exists'/'exist' are claim words when the claim says "there is"; 'fails'/'false' when it
    says "not". Older names are baselined."""
    lines = gen.split("\n")
    body = "\n".join(l for i, l in enumerate(lines) if i > 0 and not l.startswith("Full name"))
    gv = gen_vocab(gen) | set(words(body))
    if re.search(r"\bthere (?:is|are|exists?)\b", body):
        gv |= {"exist", "exists", "existence"}
    if re.search(r"\bnot\b|¬", body):
        gv |= {"fail", "fails", "false"}
    out = []
    for comp in W.name_words(full).split():
        for w in sorted(split_ident(comp)):
            if len(w) <= 1 or STRENGTH.match(w):  # strength words: V8
                continue
            if forms(w) & (gv | FUNCTION | vocab):
                continue
            out.append((f"{full}|nameword:{w}", f"V13: {full}: its name says '{w}', a word that is neither in the "
                        f"generated claim nor in {VOCAB} (a name may only use the claim's words or disclosed "
                        f"vocabulary; add a naming word there with a LEDGER line)"))
    return out


def duplicate(full, gen, seen):
    """D1 (run 2026-11-07T1828Z, after reading blind red team T d02, d03, d06 — not blind): a headline whose generated
    claim (everything but its heading and Full name line) is identical to an earlier section's adds no mathematics,
    only a new name and a new paraphrase — exactly the reader-facing surface the red teams attack (T d02 "there are
    two functions u", d03 a sign-flipped code span, d06 a 'threshold' name, each over a byte-identical copy of a
    registered headline proved by that headline). Rejected; restate the paraphrase of the existing headline instead."""
    lines = gen.split("\n")
    body = re.sub(r"\s+", " ", "\n".join(l for i, l in enumerate(lines) if i > 0 and not l.startswith("Full name"))).strip()
    if not body:
        return []
    if body in seen:
        return [(f"{full}|dup", f"D1: {full}: its generated claim is identical to that of {seen[body]}: a second name "
                 f"for the same statement adds only prose")]
    seen[body] = full
    return []


# the grammatical part of FUNCTION (articles, prepositions, connectives, pronouns): V14 reads the word after a numeral
# unless it is one of these
GRAMMAR = set("""
a an the of to in on at for from by with and or as is are be been being was were has have had its it itself
their they them this that these those which whose where when what than then if such some both each not no nor also
into onto over under below above between within out up down per via while whereas but here there
""".split())


def numeral_context(full, gen, para):
    """V14 (run 2026-11-07T1828Z, after reading blind red team T d02 — not blind): a numeral of a paraphrase (digits or
    a number word two…ten) that is directly followed by a content word ("two functions", "3 contours") states what it
    counts; that word (or a form of it) must occur within four tokens of the same numeral in the generated claim. V6
    compares numerals as a set and V10 binds only dimension and differentiability words: T d02 wrote "there are two
    functions u" over `∃ u` whose only 2 is the order in `ContDiffOn ℝ 2`. Years are skipped (check_prose rule 9 reads
    sources); older paraphrases are baselined."""
    lines = gen.split("\n")
    body = "\n".join(l for i, l in enumerate(lines) if i > 0 and not l.startswith("Full name"))
    p = re.sub(r"`[^`]*`", " , ", para)
    p = re.sub(r"\[[^\]]*\]", " ", p)
    toks = re.findall(r"\d+(?:\.\d+)?|[A-Za-zÀ-ÖØ-öø-ÿ]+(?:-[A-Za-z]+)*|[^\sA-Za-z\d]", p)
    gtoks = [t.lower() for t in re.findall(r"\d+(?:\.\d+)?|[A-Za-zÀ-ÖØ-öø-ÿ]+", body)]
    out = []
    for i, t in enumerate(toks):
        tl = t.lower()
        if tl == "twice" or not (re.fullmatch(r"\d+(?:\.\d+)?", t) or tl in NUMWORD):
            continue
        if re.fullmatch(r"(?:19|20)\d\d", t):
            continue
        val = t if t[0].isdigit() else str(NUMWORD[tl])
        nxt = toks[i + 1] if i + 1 < len(toks) else ""
        if not re.fullmatch(r"[A-Za-zÀ-ÖØ-öø-ÿ-]{2,}", nxt):
            continue
        w = norm(nxt.split("-")[0])
        if forms(w) & GRAMMAR:  # grammatical words only: the nouns of FUNCTION (solutions, decimals, order) count
            continue
        if any(g == val and any(forms(norm(x)) & forms(w) for x in gtoks[max(0, j - 4):j + 5])
               for j, g in enumerate(gtoks)):
            continue
        out.append((f"{full}|numctx:{val}:{w}", f"V14: {full}: its paraphrase writes '{t} {nxt}', but the generated "
                    f"claim does not use '{nxt}' next to {val}: a numeral may not count or measure something the "
                    f"statement's numeral does not"))
    return out

QU = r"(?:every|all|any|each|whenever)"
QE = r"(?:there\s+(?:is|are|exists?)(?!\s+no\b)|exists?|some)"
QTOK = re.compile(rf"(?i)\b(?:(?P<u>{QU})|(?P<e>{QE}))\b")


def quant_seq(text):
    """merged sequence of quantifier kinds ('U' universal, 'E' existential) of a text, code spans removed (V7)"""
    text = re.sub(r"`[^`]*`", " ", text)
    out = []
    for m in QTOK.finditer(text):
        k = "U" if m.group("u") else "E"
        if not out or out[-1] != k:
            out.append(k)
    return out


def name_strength(full, gen):
    """V8 (run 2026-11-07T0028Z, after blind red team R d02 — not blind): a claim-strength word in the headline's
    name (every component after `Checked.<Area>.`: unique, exact, sharp, optimal, …, the STRENGTH list) must be a
    word of the generated claim. R d02 registered the existence statement as `gelfand_pde_radial_unique_solution`:
    V1 no longer counts names as claim words, so nothing read the name's 'unique' against the statement."""
    lines = gen.split("\n")
    body = "\n".join(l for i, l in enumerate(lines) if i > 0 and not l.startswith("Full name"))
    # the heading and the Full name line are the name itself: before run 2026-11-07T1428Z they were read as claim
    # words, so V8 never fired (judge of R d02 on main: `…_unique_solution` over ∃ accepted)
    gv = gen_vocab(gen) | set(words(body))
    out = []
    for w in W.name_words(full).split():
        w = norm(w)
        if w.startswith("unique") and re.search(r"\bexactly one\b", body):
            continue  # Claims.lean prints ∃! as "there is exactly one"
        if STRENGTH.match(w) and not (forms(w) & gv):
            out.append((f"{full}|name:{w}", f"V8: {full}: its name says '{w}', a claim-strength word the generated "
                        f"claim does not contain: the name may not claim more than the statement"))
    return out[:1]


def order(full, gen, para):
    """V7: the paraphrase's quantifier order is a subsequence of the generated claim's"""
    lines = gen.split("\n")
    body = "\n".join(l for i, l in enumerate(lines) if i > 0 and not l.startswith("Full name"))
    # the claim's own order first, then the order inside the program definitions it names (a refutation
    # `¬ printedClaim` carries its quantifiers in the definition body)
    claim, _, defs = body.partition("Program definitions in this claim")
    g, p = quant_seq(claim) + quant_seq(defs), quant_seq(para)
    it = iter(g)
    if all(x in it for x in p):
        return scope(full, claim + defs, para)
    return [(f"{full}|order:{''.join(p)}", f"V7: {full}: its paraphrase quantifies in the order {'-'.join(p) or '-'} "
             f"(U = every/all/any/each, E = there is/exists/some), which the generated claim's order "
             f"{'-'.join(g) or '(none)'} does not contain: write the quantifiers in the claim's order")]


BINDER = re.compile(r"`([^`:]+?)\s*:\s*[^`]*`")
GQ = re.compile(r"(?i)(\*\*for every\*\*|for every|there is|there exists?)")


def claim_binders(text):
    """(kind, name) of every binder of the generated claim, in order: the code spans `x : T` that follow a
    quantifier phrase (comma-separated runs)"""
    out = []
    for m in GQ.finditer(text):
        kind = "E" if m.group(1).lower().startswith("there") else "U"
        rest = text[m.end():]
        while True:
            b = re.match(r"\s*,?\s*(?:and\s+)?" + BINDER.pattern, rest)
            if not b:
                break
            for v in b.group(1).split():
                out.append((kind, v))
            rest = rest[b.end():]
    return out


def scope(full, gen_text, para):
    """V7, second part (run 2026-11-07T0028Z, after blind red team R d01 — not blind): a universal and an
    existential the paraphrase attaches to named binders of the claim keep the claim's relative order. R d01
    wrote ∀ε ∀x ∃N ∀n as "for every ε there is N such that, for every x …": kind order U-E-U is a subsequence,
    but x moved behind N (a uniform N)."""
    binders = claim_binders(gen_text)
    pos = {}
    for i, (k, v) in enumerate(binders):
        pos.setdefault(v, (i, k))
    if not pos:
        return []
    text = re.sub(r"`([^`]*)`", lambda m: " " + " ".join(re.findall(r"[^\W\d_][\w'₀-₉]*", m.group(1))) + " ", para)
    ms = list(QTOK.finditer(text))
    att = []
    for j, m in enumerate(ms):
        end = ms[j + 1].start() if j + 1 < len(ms) else len(text)
        window = text[m.end():min(end, m.end() + 40)]
        window = re.split(r"[,;:.]|\bsuch that\b|\bwith\b|\bif\b", window)[0]
        kind = "U" if m.group("u") else "E"
        for t in re.findall(r"[^\W\d_][\w'₀-₉]*", window):
            if t in pos and pos[t][1] == kind:
                att.append((kind, t))
                break
    for a in range(len(att)):
        for b in range(a + 1, len(att)):
            (k1, v1), (k2, v2) = att[a], att[b]
            if k1 != k2 and pos[v1][0] > pos[v2][0]:
                return [(f"{full}|scope:{v1}-{v2}", f"V7: {full}: its paraphrase quantifies {v1} ({k1}) before {v2} ({k2}), "
                         f"but the generated claim binds {v2} before {v1}: the order of a universal and an existential "
                         f"changes what is claimed")]
    return []


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
    # positive and negative controls first (run 2026-11-07T1428Z: V8 shipped dead and nothing noticed): every rule
    # must reject its own control defect and accept the clean twin (scripts/trust/controls/prose_rule_controls.py)
    sys.path.insert(0, str(Path(__file__).resolve().parent / "controls"))
    import prose_rule_controls  # noqa: E402
    if prose_rule_controls.main() != 0:
        print("check_claim_vocab: FAIL (a rule failed its control; see above)")
        return 1
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
