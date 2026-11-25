#!/usr/bin/env python3
"""Reader material of test AZ (run 2026-11-25T2028Z; brief runs/2026-11-25T2028Z/t5/reader_brief_AZ.md).

Three versions (O, V, E) of AY's d04 material (header + the entry of lookback_second_order_bigO), differing only in the
header's sentence on objections and the entry's objection clause. Asserted replacements: each must occur once."""
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[3]
SRC = ROOT / "runs/2026-11-25T1428Z/t5/reader_material/d04.md"
OUT = ROOT / "runs/2026-11-25T2028Z/t5/reader_material"

HEAD_OLD = ("are not printed: the record shows that it is open and where it is written; no entry can mark it settled.")
HEAD_V = ("are not printed: the record shows that it is open and where it is written. An objection is closed only by a\n"
          "referee verdict file committed alone under `runs/` and named in the registry; the record then shows that it is\n"
          "closed and the path of that file (the verdict's words are author prose and are not printed either).")
HEAD_E = ("are not printed: the record shows that it is open and where it is written. An objection is closed only by a\n"
          "Lean theorem in `Checked` stating that a blind reader's statement of the source claim (written from the source\n"
          "alone, its brief committed before it) is equivalent to the headline's statement, proved without any theorem of\n"
          "this program (only its definitions and Mathlib: the generator of this page checks every constant of the proof\n"
          "and fails otherwise); the record then shows that it is closed and the name of that theorem.")

ENT_OLD = ("OPEN FIDELITY OBJECTIONS on record (`scripts/trust/objections.txt`): 1: raised in run 2026-11-25T1528Z, its text "
           "written in `runs/2026-11-25T1528Z/referee_note_lookback.md` (author prose, not printed on this page);")
ENT_V = ("fidelity objections on record (`scripts/trust/objections.txt`): 1, closed: raised in run 2026-11-25T1528Z, its "
         "text written in `runs/2026-11-25T1528Z/referee_note_lookback.md` (author prose, not printed on this page); "
         "closed by the referee verdict written in `runs/2026-11-25T2028Z/verdict_lookback.md` (author prose, not "
         "printed on this page); open fidelity objections: none;")
ENT_E = ("fidelity objections on record (`scripts/trust/objections.txt`): 1, closed: raised in run 2026-11-25T1528Z, its "
         "text written in `runs/2026-11-25T1528Z/referee_note_lookback.md` (author prose, not printed on this page); "
         "closed by the Checked theorem `Checked.Trust.Closures.lookback_second_order_bigO_reading`: a blind reader's "
         "statement of the source claim (brief `runs/2026-11-25T2028Z/closures/brief_lookback.md`, committed before "
         "the reading) is equivalent to this statement, by a proof that uses no theorem of this program; open fidelity "
         "objections: none;")


def main():
    t = SRC.read_text(encoding="utf-8")
    for s in (HEAD_OLD, ENT_OLD):
        if t.count(s) != 1:
            sys.exit(f"expected once: {s[:60]}")
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "O.md").write_text(t, encoding="utf-8")
    (OUT / "V.md").write_text(t.replace(HEAD_OLD, HEAD_V).replace(ENT_OLD, ENT_V), encoding="utf-8")
    (OUT / "E.md").write_text(t.replace(HEAD_OLD, HEAD_E).replace(ENT_OLD, ENT_E), encoding="utf-8")
    print("wrote", ", ".join(sorted(p.name for p in OUT.iterdir())))


if __name__ == "__main__":
    main()
