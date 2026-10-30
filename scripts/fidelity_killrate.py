#!/usr/bin/env python3
"""Trust metric T1: mutation kill rate of the definition specifications in Work/Fidelity.

A mutant is a `def` documented as a wrong definition (author mutants `m*` in *Spec.lean,
blind red-team mutants `rt*` in RedTeam*.lean). It is killed when a theorem
`reject_<name> : ¬ <Spec> <name>` exists. The Lean build (CI) is what checks the proofs;
this script only counts, and reports surviving mutants (specification gaps).
Usage: python3 scripts/fidelity_killrate.py
"""
import pathlib, re
root = pathlib.Path(__file__).resolve().parent.parent / "Work" / "Fidelity"
text = {p.name: p.read_text() for p in sorted(root.glob("*.lean"))}
allsrc = "\n".join(text.values())
rejected = set(re.findall(r"theorem reject_(\w+)\s*:\s*¬", allsrc))
rows = []
for name, src in text.items():
    if name.startswith("RedTeam") and not name.endswith("Check.lean"):
        kind, muts = "blind", re.findall(r"def (rt\d+)\b", src)
    elif name.endswith("Spec.lean"):
        kind, muts = "author", re.findall(r"def (m[A-Z]\w*)\b", src)
    else:
        continue
    for m in muts:
        rows.append((kind, name, m, m in rejected))
for kind in ("blind", "author"):
    sel = [r for r in rows if r[0] == kind]
    k = sum(r[3] for r in sel)
    print(f"{kind}: {k}/{len(sel)} killed")
    for r in sel:
        if not r[3]:
            print(f"  SURVIVOR {r[1]}:{r[2]}")
