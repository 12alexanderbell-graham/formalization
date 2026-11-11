# Fork A: certified event chains for the separation problem (run 2026-11-11T0232Z)

Field: clamped adverse-sign coefficient-K field `Work.FSSep.SBase.vS K` (q' = −K f q + 1 − p²), start (0, 0, 0).

Commands (repository root; JSON outside the repository):
- `FS_K=10000000000/1988377351 python3 runs/2026-11-11T0232Z/scripts/gen_sep_wc.py 0 4 32 12 18 1/2 2 over /tmp/claude-0/sep/j/over.json`
  → 128 cells, h = 1/32, degree 12, coefficients 10⁻¹⁸, end margin p − 1 = 2.29·10⁻¹¹, final B 4.7·10⁻¹⁶, amplification e^3.56.
- `FS_THETA=11/15 FS_K=10000000000/1988377350 python3 runs/2026-11-11T0232Z/scripts/gen_sep_wc.py 0 33/8 32 12 18 1/2 2 slowp /tmp/claude-0/sep/j/slow.json`
  → 132 cells, path margin (1 − p) 5.36·10⁻¹¹, end margins 0 ≤ p: 1.0, 3(1 − p) − q: 7.81·10⁻¹¹, f − 11/15: 2.34, amplification e^3.59.
- `python3 runs/2026-11-11T0232Z/scripts/port_scellwc.py` → `Work/FSSep/SCellWC.lean` (port of `Work/FSNeg/NCellWC.lean`: coefficient 10 → rational K with 0 ≤ K checked in `CellProp`; `os_neg` for real K; endSl threshold 11/15; every replacement asserted).
- `python3 runs/2026-11-11T0232Z/scripts/emit_sep_wc.py /tmp/claude-0/sep/j/over.json 8 Work/FSSep/SOverLo.lean SOverLo 10000000000/1988377351`
- `python3 runs/2026-11-11T0232Z/scripts/emit_sep_wc.py /tmp/claude-0/sep/j/slow.json 8 Work/FSSep/SSlowHi.lean SSlowHi 10000000000/1988377350`
  (SEG = 8: 16 and 17 `decide +kernel` segments; the K literal in `chain` is written as given, not reduced.)

Lean (2 cores): `lake env lean Work/FSSep/SCellWC.lean` 64 s; `lake build Work.FSSep.SOverLo` 102 s; `lake build Work.FSSep.SSlowHi` 120 s (built one at a time).
Axioms of both `chain` theorems: propext, Classical.choice, Quot.sound.

Theorems:
- `Work.FSSep.SOverLo.chain : ChainK (10000000000 / 1988377351) Over` (η = 4)
- `Work.FSSep.SSlowHi.chain : ChainK (10000000000 / 1988377350) SlowS` (η = 33/8)
