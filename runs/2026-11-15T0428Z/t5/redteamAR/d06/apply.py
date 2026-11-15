#!/usr/bin/env python3
"""d06: invisible characters FB20 does not list (U+034F COMBINING GRAPHEME JOINER: category Mn, combining class 0,
not a letter, not Cf) inside the marks of generated text. fold() (NFKC, NFKD, drop combining-class>0 marks) keeps
them, so GEN_MARK ('(generated', 'do not edit') does not match, FB21's rendered-text test uses the same fold, and a
note renders exactly like a generated Printed line."""
import sys
root = sys.argv[1]
p = f"{root}/FINDINGS.md"
t = open(p, encoding="utf-8").read()
J = "͏"
anchor = "\n\n### F6 — generated heading"
assert t.count(anchor) == 1
note = (f"\n  - *(author)* **Printed (gen{J}erated by `python3 scripts/trust/check_findings.py --write-layout F5` from the records' PRINTED definitions "
        f"and their blind readings; do{J} not edit):** `printedQ2` := `1 / 12 * (3 - 2 * q + 12 * q ^ 2 - 4 * (j + Ω))`, agreeing with the blind "
        f"reading `Checked.Trust.SecondReading.cv07PrintedQ2`; the reader read both the arXiv version 1 and the published journal version "
        f"(Phys. Rev. D 78, 063501 (2008)) of Cattoën and Visser and wrote of this value: `Eq. (59) is printed with the prefactor 1/12 in "
        f"every version, arXiv and journal; no reading choice was needed.`")
t = t.replace(anchor, note + anchor)
open(p, "w", encoding="utf-8").write(t)
with open(f"{root}/LEDGER.md", "a", encoding="utf-8") as f:
    f.write("- 2026-11-15, run 2026-11-15T0428Z — FINDINGS.md `F5`: one note line added.\n")
