#!/usr/bin/env python3
"""Phrase-only judge (run 2026-11-08T1828Z): apply each defect's apply.py to a scratch copy of the tree's
phrases.txt and LEDGER.md, rebuild the linter's entries from .lake/phrases.jsonl (spec_text and rests_on do not
depend on phrases: no Lean changes in these defects) with the defect's phrases, and run every rule of
scripts/trust/check_claims.py (glossary attribution, U1, P1, U2, P2 with its baseline). Prints, per defect, the
problems that name a definition whose phrase the defect changed.
usage: judge_phrases.py <tree> <defect dir> [<defect dir> ...]"""
import json, os, re, shutil, subprocess, sys, tempfile
tree = os.path.abspath(sys.argv[1])
sys.path.insert(0, os.path.join(tree, "scripts/trust"))
import check_claims as cc
E0 = [json.loads(l) for l in open(os.path.join(tree, ".lake/phrases.jsonl")) if l.strip()]
base_ph = cc.parse_phrases(open(os.path.join(tree, "scripts/trust/phrases.txt"), encoding="utf-8").read())
for dd in sys.argv[2:]:
    tmp = tempfile.mkdtemp()
    os.makedirs(os.path.join(tmp, "scripts/trust"))
    for f in ("scripts/trust/phrases.txt", "LEDGER.md", "CLAIMS.md", "scripts/trust/glossary.txt"):
        shutil.copy(os.path.join(tree, f), os.path.join(tmp, f))
    r = subprocess.run([sys.executable, os.path.join(dd, "apply.py"), tmp], capture_output=True, text=True)
    name = os.path.basename(dd.rstrip("/"))
    if r.returncode:
        print(f"{name}: apply.py FAILED on this tree: {r.stderr.strip().splitlines()[-1] if r.stderr.strip() else ''}")
        continue
    ph = cc.parse_phrases(open(os.path.join(tmp, "scripts/trust/phrases.txt"), encoding="utf-8").read())
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
    probs += cc.spec_vocabulary(ents, cc.p2_baseline())
    hits = [p for p in probs if any(p.startswith(n) or p.split(":")[0].endswith("." + n) or p.split(":")[0] == n for n in changed)]
    print(f"{name}: phrases changed {sorted(changed)} -> {'REJECTED' if hits else 'passes the phrase rules'}")
    for h in hits:
        print("    " + h[:300])
    shutil.rmtree(tmp)
