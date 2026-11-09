#!/usr/bin/env python3
"""Phrase-only judge for blind red team AA (run 2026-11-09T0228Z), from runs/2026-11-08T2228Z/t5/scripts/judge_Z.py.
Differences: the defect may edit scripts/trust/phrase_roles.txt (d03, d04 delete registry lines), so the registry is
copied into the scratch tree and read from there; when the tree's check_claims.py has P7/P8 (coverage,
registry_complete, registry_removals) they are run too, with the tree's own registry as the --base registry.
usage: judge_AA.py <tree> <defect dir> [...]   (PHRASES_JSONL=<file> overrides <tree>/.lake/phrases.jsonl)"""
import json, os, shutil, subprocess, sys, tempfile
tree = os.path.abspath(sys.argv[1])
sys.path.insert(0, os.path.join(tree, "scripts/trust"))
import check_claims as cc
E0 = [json.loads(l) for l in open(os.environ.get("PHRASES_JSONL", os.path.join(tree, ".lake/phrases.jsonl"))) if l.strip()]
base_ph = cc.parse_phrases(open(os.path.join(tree, "scripts/trust/phrases.txt"), encoding="utf-8").read())
base_reg = open(os.path.join(tree, cc.ROLES), encoding="utf-8").read()
for dd in sys.argv[2:]:
    tmp = tempfile.mkdtemp()
    os.makedirs(os.path.join(tmp, "scripts/trust"))
    for f in ("scripts/trust/phrases.txt", "LEDGER.md", "scripts/trust/glossary.txt", cc.ROLES):
        shutil.copy(os.path.join(tree, f), os.path.join(tmp, f))
    r = subprocess.run([sys.executable, os.path.join(dd, "apply.py"), tmp], capture_output=True, text=True)
    name = os.path.basename(dd.rstrip("/"))
    if r.returncode:
        print(f"{name}: apply.py FAILED on this tree: {r.stderr.strip().splitlines()[-1] if r.stderr.strip() else ''}")
        continue
    ph = cc.parse_phrases(open(os.path.join(tmp, "scripts/trust/phrases.txt"), encoding="utf-8").read())
    reg = open(os.path.join(tmp, cc.ROLES), encoding="utf-8").read()
    changed = {k for k in ph if base_ph.get(k) != ph[k]} | {k for k in base_ph if k not in ph}
    ents = []
    for e in E0:
        k = [k for k in ph if e["name"] == k or e["name"].endswith("." + k)]
        if k:
            ents.append(dict(e, phrase=ph[k[0]]))
    probs = []
    for e in ents:
        for rx, names in cc.glossary():
            m = rx.search(e["phrase"])
            if m and not (names & {e["short"], *e["rests_on"]}):
                probs.append(f"{e['name']}: glossary '{m.group(0)}' not attributed")
    probs += cc.duplicate_phrases(ph) + cc.formula_in_phrase(ph) + cc.head_noun(ents, cc.glossary())
    if hasattr(cc, "load_registry"):
        rl, sg, cl, rb = cc.load_registry(reg)
        probs += rb + cc.role_binding(ph, rl, sg) + cc.coverage(ph, rl, sg, cl)
        probs += [f"{changed and sorted(changed)[0]}: {x}" for x in cc.registry_complete(ph, reg)]
        probs += [f"{changed and sorted(changed)[0]}: --base {x}" for x in cc.registry_removals("BASE", base_reg, reg, ph)]
        probs += cc.spec_vocabulary(ents, cc.p2_baseline() | cc.p5_baseline(), rl, sg, cl)
    else:
        rl, sg, rb = cc.load_roles(reg)
        probs += rb + cc.role_binding(ph, rl, sg) + cc.spec_vocabulary(ents, cc.p2_baseline() | cc.p5_baseline(), rl, sg)
    hits = [p for p in probs if any(p.startswith(n) or p.split(":")[0].endswith("." + n) or p.split(":")[0] == n for n in changed)]
    print(f"{name}: phrases changed {sorted(changed)} -> {'REJECTED' if hits else 'passes the phrase rules'}")
    for h in hits:
        print("    " + h[:300])
    shutil.rmtree(tmp)
