#!/usr/bin/env python3
"""Trust metric T1: mutation kill rate of the definition specifications in Work/Fidelity.

A mutant is a `def` documented as a wrong definition (author mutants `m*` in *Spec.lean,
blind red-team mutants `rt*` in RedTeam*.lean). It is killed when a theorem
`reject_<name> : ¬ <Spec> <name>` exists. The Lean build (CI) is what checks the proofs;
this script only counts, and reports surviving mutants (specification gaps).
Usage: python3 scripts/fidelity_killrate.py
"""
import pathlib, re
# Mutants equal to the true definition on the physical domain fixed by the red-team brief
# (documented in the *Check.lean headers); reported, not scored.
EXCLUDED = {"rq4": "differs only where adot = 0 (q undefined)",
            "ra5": "differs only for t > t0 (outside the admissible domain)"}
base = pathlib.Path(__file__).resolve().parent.parent
text = {}
for d in ("Checked/Fidelity", "Work/Fidelity"):
    for p in sorted((base / d).glob("*.lean")):
        text[p.name] = p.read_text()
allsrc = "\n".join(text.values())
rejected = set(re.findall(r"theorem reject_(\w+)\s*:\s*¬", allsrc))
rows = []
for name, src in text.items():
    if name.startswith("RedTeam") and not name.endswith("Check.lean"):
        kind, muts = "blind", re.findall(r"def (r[a-zA-Z]{0,2}\d+)\b", src)
    elif name.endswith("Spec.lean"):
        kind, muts = "author", re.findall(r"def (m[A-Z]\w*)\b", src)
    else:
        continue
    for m in muts:
        if m in EXCLUDED:
            print(f"excluded {name}:{m}: {EXCLUDED[m]}")
            continue
        rows.append((kind, name, m, m in rejected))
for kind in ("blind", "author"):
    sel = [r for r in rows if r[0] == kind]
    k = sum(r[3] for r in sel)
    print(f"{kind}: {k}/{len(sel)} killed")
    for r in sel:
        if not r[3]:
            print(f"  SURVIVOR {r[1]}:{r[2]}")

# Pinning: a theorem `<spec>_pins` proves that every function meeting the spec equals the
# program's definition on the admissible domain (no mutant can survive it there).
specs = sorted(set(re.findall(r"structure (\w+Spec\d?)\b", allsrc)))
pins = set(m.lower() for m in re.findall(r"theorem (\w+)_pins\b", allsrc))
for sp in specs:
    key = sp[0].lower() + sp[1:]
    print(f"spec {sp}: {'PINS the definition' if key.lower() in pins else 'anchors only (does not pin)'}")
