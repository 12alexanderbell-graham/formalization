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
Exit status 1 if any STRENGTH word is found (NEW words are advisory). Not a CI check: the binding checks
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
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
