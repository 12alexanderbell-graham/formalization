#!/usr/bin/env python3
"""Run 2026-11-26T1428Z (part 3): how far does a blind literal reading travel from the statement it was read for?

A reader constant (a `def` of a `Checked/Trust/SecondReading*` module) covers the literals of every headline it is
registered for in `scripts/trust/literal_readings.txt` whose statement contains its body. Rule 1 (d) of
check_literals.py confines one-numeral binder constants to headlines of the same model as a baselined anchor; any
other constant may be registered for any headline whose statement it matches (red team AY's `brute.py`).

This script (needs `.lake/*.jsonl` of a StatementDeps run) reports:
  A. current registrations: constants registered for several headlines, and pairs whose headline shares no model
     module (`same_model`) with any other headline the constant is registered for;
  B. reach: for every reader constant with a numeral and every headline not registered with it whose statement it
     matches (strict span coverage of at least one numeral), whether that headline shares a model with a headline
     the constant is registered for. A match outside every model of its registrations is a reading of another
     source reused.
Usage: python3 runs/2026-11-26T1428Z/scripts/measure_reuse.py   (from the repository root)
"""
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts/trust"))
import check_literals as L  # noqa: E402

rows = L.load_rows()
heads = {r["name"]: r for r in rows if r.get("type") == "headline"}
errors = []
consts = L.reader_constants()
readings = L.load_readings(heads, errors)
L.LOOSE_PAIRS = L.pair_baseline(L.LOOSE_BL)

reg = {}  # constant -> registered headlines
for h, regs in readings.items():
    for c, _ in regs:
        reg.setdefault(c, set()).add(h)

print("A. registrations:", sum(len(v) for v in reg.values()), "pairs,", len(reg), "constants;",
      sum(1 for v in reg.values() if len(v) > 1), "constants registered for more than one headline")
cross = []
for c, hs in sorted(reg.items()):
    if len(hs) < 2:
        continue
    for h in sorted(hs):
        others = [o for o in hs if o != h]
        if not any(L.same_model(heads[h], heads[o]) for o in others):
            cross.append((c, h))
for c, h in cross:
    print("  cross-model registration:", c.split(".")[-1], "->", h.split(".")[-1])
print("  cross-model registrations:", len(cross))

reach_same, reach_cross, unreg = 0, [], 0
for c, const in sorted(consts.items()):
    if not any(L.is_num(t) for t in const[1]):
        continue
    hs = reg.get(c, set())
    if not hs:
        unreg += 1
        continue
    for h, row in heads.items():
        if h in hs:
            continue
        try:
            toks = L.lex(L.statement_text(row["module"], row["name"]))
            spans = L.covered_spans(toks, const, True)
        except Exception:
            continue
        if not any(L.is_num(toks[j]) for sp in spans for j in sp):
            continue
        if any(L.same_model(row, heads[o]) for o in hs):
            reach_same += 1
        else:
            reach_cross.append((c, h))
print("B. reader constants with a numeral not registered anywhere:", unreg)
print("   unregistered matches in a model of the constant's registrations:", reach_same)
print("   unregistered matches outside every model of its registrations:", len(reach_cross))
for c, h in reach_cross:
    print("    ", c.split(".")[-1], "would cover", h.split(".")[-1])
