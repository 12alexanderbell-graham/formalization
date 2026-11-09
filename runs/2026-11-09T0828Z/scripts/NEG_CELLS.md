# Fork C: certified event chains, adverse-sign K = 10 field (run 2026-11-09T0828Z)

Commands (from the repository root; JSON to /tmp):
- `FS_K=10 python3 runs/2026-11-09T0828Z/scripts/gen_neg_wc.py 1/2 5/4 16 10 12 1/2 2 slow /tmp/negc/half.json` (20 cells, end margins 0.82 / 0.34 / 0.19, path margin 0.178)
- `… 3/4 9/8 16 10 12 1/2 2 slow /tmp/negc/34.json` (18 cells, end margins 0.89 / 0.119 / 0.20, path margin 0.108)
- `… 11/10 5/4 16 10 12 1/2 2 over /tmp/negc/11.json` (20 cells, end margin p − 1 = 0.0226)
- `python3 runs/2026-11-09T0828Z/scripts/emit_neg_wc.py /tmp/negc/half.json 10 Work/FSNeg/NSlowHalf.lean NSlowHalf "1 / 2"` (34: SEG 9, `NSlow34`, "3 / 4"; 11: SEG 10, `NOver11`, "11 / 10").
Arguments: A, L, 1/h, Taylor degree, rounding digits, w1, w2, mode, out. Every cell checked in exact Fractions before emission.
Lean: `Work/FSNeg/NCellWC.lean` (port of `Work/FSTenth/F10CellWC.lean`: defect3, SolC, Sylvester corners at s' = −(y2 + P2) via `os_neg`; new `sideS`, `sideS_spec`, `sideT`, `endSl`, `endSl_q0`, `endO_q0`), build 46 s; NSlowHalf 37 s, NSlow34 81 s, NOver11 82 s (lake build, parallel).
