#!/usr/bin/env python3
"""Name a headline at freeze time so that its promotion does not have to rename it (run 2026-11-15T0228Z, annex LIV).

Why: run 2026-11-15T0028Z froze `Work.Math.BonnorEbertAll.bonnor_ebert_all_extrema`; at promotion (run 0228Z)
check_claim_vocab.py V8 rejected the strength word 'all' in the name (every component after `Checked.<Area>.`,
the module included) and V13 the word 'extrema' (not in the generated claim or prose_vocab.txt). The promotion
had to rename module and theorem, re-relock and regenerate CLAIMS (≈ 25 min). The name rules are known before
the claim exists, so read the proposed name with the same word lists when freezing.

  python3 scripts/trust/check_freeze_name.py <Lean name> [<Lean name> ...]
  python3 scripts/trust/check_freeze_name.py --file Work/Math/X.lean      every theorem name in the file

Reports, per name word (split as check_claim_vocab.py splits names):
  STRENGTH  a V8 strength word ('all', 'every', 'global', 'unique', 'exact', …): fails at promotion unless the
            generated claim itself contains the word — rename before freezing;
  NEW       a word that is not a FUNCTION word and not in scripts/trust/prose_vocab.txt: passes V13 only if the
            generated claim contains it (Lean identifiers such as `StrictMono` count, split), otherwise it needs
            a prose_vocab.txt line with a LEDGER line.
With --file, also (run 2026-11-20T2228Z, annex LIV; see LEDGER) the headline docstring's words are read as V1 reads
the paraphrase CLAIMS.md will print, against a proxy of the generated claim (the words of the identifiers in the
statement's own source):
  DOCWORD   a docstring word that is not a FUNCTION word, not in prose_vocab.txt and not a word of an identifier of
            the statement: V1 fails at promotion unless the generated claim happens to contain it — reword it
            before freezing (run 2026-11-20T2228Z: 'classical', 'symmetry' cost a second ten-minute relock).
With --file, also (run 2026-11-26T0428Z, annex LIV; see LEDGER) numerals of a statement raised to, or multiplied
by, a power of a variable (`23 / 10 * (21 / 50) ^ n`) are reported:
  LITERAL   such a numeral is on a comparison side that is not numerals only, so it is no certified target
            (check_literals.py a2) and needs a blind literal reading, whose brief would have to state the program's
            own constant (check_brief_leak.py fails it). Restate before freezing: bound existential constants by
            numeral-only sides (`∃ c q : ℝ, c ≤ 23 / 10 ∧ 0 ≤ q ∧ q ≤ 21 / 50 ∧ ∀ n, … ≤ c * q ^ n`); run 0428Z
            froze the first form and needed a second freeze and a second reader.
Exit status 1 if any STRENGTH word is found (NEW and DOCWORD are advisory). Not a CI check: the binding checks
are V8/V13 of check_claim_vocab.py on the promoted headline.
"""
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_claim_vocab as V  # noqa: E402
import check_claim_words as W  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]


def names_in(path):
    text = Path(path).read_text()
    ns = re.findall(r"^namespace\s+(\S+)", text, re.M)
    prefix = ns[0] + "." if ns else ""
    return [prefix + n for n in re.findall(r"^\s*(?:theorem|lemma)\s+(\S+)", text, re.M)]


def docs_in(path):
    """(theorem name, docstring, statement source) for every documented theorem of the file."""
    text = Path(path).read_text()
    ns = re.findall(r"^namespace\s+(\S+)", text, re.M)
    prefix = ns[0] + "." if ns else ""
    out = []
    for m in re.finditer(r"/--(.*?)-/\s*(?:@\[[^\]]*\]\s*)?(?:theorem|lemma)\s+(\S+)(.*?):=", text, re.S):
        out.append((prefix + m.group(2), m.group(1), m.group(3)))
    return out


def doc_words(doc, stmt, vocab):
    # words Claims.lean's templates print in every generated claim ('for every', 'there is', 'assuming', 'then')
    proxy = {"every", "there", "is", "assuming", "then", "such", "that", "if", "not", "for"}
    for ident in re.findall(r"[A-Za-z][A-Za-z0-9_.']*", stmt):
        for comp in ident.split("."):
            proxy |= {V.norm(w) for w in V.split_ident(comp)}
            proxy.add(V.norm(comp))
    bad = []
    for w in V.words(doc):
        if len(w) <= 1 or w in bad:
            continue
        f = V.forms(w)
        if f & proxy or f & V.FUNCTION or f & vocab:
            continue
        bad.append(w)
    return bad


NUMGROUP = r"(?:\d+(?:\.\d+)?(?:\s*/\s*\d+(?:\.\d+)?)?|\(\s*\d+(?:\.\d+)?\s*/\s*\d+(?:\.\d+)?\s*\))"
POWLIT = re.compile(NUMGROUP + r"(?:\s*\*\s*" + NUMGROUP + r")?\s*(?:\*\s*[^\W\d][\w₀-₉']*\s*)?\^\s*[^\W\d][\w₀-₉']*")


def power_literals(stmt):
    """Spans where a numeral is raised to, or multiplies, a power of a variable (advisory; see LITERAL)."""
    flat = re.sub(r"\s+", " ", stmt)
    return [m.group(0).strip() for m in POWLIT.finditer(flat)]


def main(argv):
    if not argv:
        print(__doc__)
        return 2
    names = names_in(argv[1]) if argv[0] == "--file" else argv
    vocab = V.load_set(V.VOCAB)
    bad = 0
    for full in names:
        strength, new = [], []
        for comp in W.name_words(full).split():
            for w in sorted(V.split_ident(comp)):
                if len(w) <= 1:
                    continue
                if V.STRENGTH.match(w):
                    strength.append(w)
                elif not (V.forms(w) & (V.FUNCTION | vocab)):
                    new.append(w)
        if strength:
            bad += 1
        status = "STRENGTH " + ",".join(sorted(set(strength))) if strength else "ok"
        extra = ("; NEW " + ",".join(sorted(set(new)))) if new else ""
        print(f"{full}: {status}{extra}")
    if argv[0] == "--file":
        for full, doc, stmt in docs_in(argv[1]):
            dw = doc_words(doc, stmt, vocab)
            print(f"{full}: docstring " + ("ok" if not dw else "DOCWORD " + ",".join(dw)))
            lits = power_literals(stmt)
            print(f"{full}: literals " + ("ok" if not lits else "LITERAL " + " | ".join(lits)))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
