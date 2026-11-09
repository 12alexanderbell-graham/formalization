#!/usr/bin/env python3
"""Phrase-only judge for blind red team AC (run 2026-11-09T1428Z), from runs/2026-11-09T0228Z/t5/judge_AA.py.
Applies each defect to scratch copies of phrases.txt, the registry, the exclusion baseline and LEDGER.md of <tree>
and runs every phrase rule of <tree>'s check_claims.py that needs no Lean output: U1, P1, P3/P4/P6, P7, P8 (lint and
--base, the unmodified tree as base), and when present P9 baseline growth, P10/P11 (`generated`) and P12
(`baseline_reentry`). Glossary U2 and P2 need .lake/phrases.jsonl (Claims.lean) and are run separately.
The unmodified tree must give 0 problems (printed as 'control'). Any problem rejects the defect.
usage: judge_AC.py <tree> <defect dir> [...]"""
import os, shutil, subprocess, sys, tempfile
tree = os.path.abspath(sys.argv[1])
sys.path.insert(0, os.path.join(tree, "scripts/trust"))
import check_claims as cc
F = ["scripts/trust/phrases.txt", cc.ROLES, "scripts/trust/phrase_clause_baseline.txt", "LEDGER.md"]
rd = lambda root, f: open(os.path.join(root, f), encoding="utf-8", newline="").read()
base = {f: rd(tree, f) for f in F}


def problems(t):
    ph = cc.parse_phrases(t[F[0]])
    reg = t[F[1]]
    rl, sg, cl, rb = cc.load_registry(reg)
    p = rb + cc.duplicate_phrases(ph) + cc.formula_in_phrase(ph) + cc.role_binding(ph, rl, sg)
    p += cc.coverage(ph, rl, sg, cl, cc.registry_names(reg))
    p += cc.registry_complete(ph, reg, cc.clause_baseline(t[F[2]]))
    p += ["--base " + x for x in cc.registry_removals("BASE", base[F[1]], reg, ph)]
    grown = cc.clause_baseline(t[F[2]]) - cc.clause_baseline(base[F[2]])
    p += [f"--base P9 baseline grown: {x}" for x in sorted(grown)]
    if hasattr(cc, "generated"):
        p += cc.generated(t[F[0]], reg)
    if hasattr(cc, "baseline_reentry"):
        p += ["--base " + x for x in cc.baseline_reentry("BASE", base[F[2]], base[F[1]], reg)]
    old = cc.parse_phrases(base[F[0]])
    changed = sorted(d for d in set(old) | set(ph) if old.get(d) != ph.get(d))
    led = t[F[3]][len(base[F[3]]):]
    for d in changed:
        if d.split(".")[-1] not in led:
            p.append(f"--base phrase {d} changed without a LEDGER line")
    return p, changed


c, _ = problems(base)
print(f"control (unmodified tree): {len(c)} problems" + "".join("\n    " + x[:300] for x in c))
for dd in sys.argv[2:]:
    tmp = tempfile.mkdtemp()
    for f in F:
        os.makedirs(os.path.dirname(os.path.join(tmp, f)) or tmp, exist_ok=True)
        shutil.copy(os.path.join(tree, f), os.path.join(tmp, f))
    name = os.path.basename(dd.rstrip("/"))
    r = subprocess.run([sys.executable, os.path.join(dd, "apply.py"), tmp], capture_output=True, text=True)
    if r.returncode:
        print(f"{name}: apply.py FAILED: {r.stderr.strip().splitlines()[-1] if r.stderr.strip() else ''}")
        continue
    p, changed = problems({f: rd(tmp, f) for f in F})
    print(f"{name}: phrases changed (as check_claims parses them) {changed} -> {'REJECTED' if p else 'passes the phrase rules'}")
    for h in p:
        print("    " + h[:300])
    shutil.rmtree(tmp)
