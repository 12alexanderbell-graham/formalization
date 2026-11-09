#!/usr/bin/env python3
"""Judge for adversary AD (run 2026-11-09T1428Z): like judge_AC.py, but each defect is applied to a scratch copy of
<tree>'s scripts/, runs/ and LEDGER.md (AD's defects add reader files and regenerate phrases with the copy's own
`check_claims.py --generate`), and the copy's own check_claims.py judges it (ROOT = the copy), with <tree> as base.
usage: judge_AD.py <tree> <defect dir> [...]"""
import importlib.util, os, shutil, subprocess, sys, tempfile
tree = os.path.abspath(sys.argv[1])
F = ["scripts/trust/phrases.txt", "scripts/trust/phrase_roles.txt", "scripts/trust/phrase_clause_baseline.txt", "LEDGER.md"]
rd = lambda root, f: open(os.path.join(root, f), encoding="utf-8", newline="").read()
base = {f: rd(tree, f) for f in F}


def load(root):
    spec = importlib.util.spec_from_file_location(f"cc_{abs(hash(root))}", os.path.join(root, "scripts/trust/check_claims.py"))
    m = importlib.util.module_from_spec(spec)
    sys.path.insert(0, os.path.join(root, "scripts/trust"))
    spec.loader.exec_module(m)
    sys.path.pop(0)
    return m


def problems(root):
    cc = load(root)
    t = {f: rd(root, f) for f in F}
    ph = cc.parse_phrases(t[F[0]])
    reg = t[F[1]]
    rl, sg, cl, rb = cc.load_registry(reg)
    p = rb + cc.duplicate_phrases(ph) + cc.formula_in_phrase(ph) + cc.role_binding(ph, rl, sg)
    p += cc.coverage(ph, rl, sg, cl, cc.registry_names(reg))
    p += cc.registry_complete(ph, reg, cc.clause_baseline(t[F[2]]))
    p += ["--base " + x for x in cc.registry_removals("BASE", base[F[1]], reg, ph)]
    p += [f"--base P9 baseline grown: {x}" for x in sorted(cc.clause_baseline(t[F[2]]) - cc.clause_baseline(base[F[2]]))]
    p += cc.generated(t[F[0]], reg)
    p += ["--base " + x for x in cc.baseline_reentry("BASE", base[F[2]], base[F[1]], reg)]
    if cc._controls():
        p.append("controls failed")
    old = cc.parse_phrases(base[F[0]])
    changed = sorted(d for d in set(old) | set(ph) if old.get(d) != ph.get(d))
    led = t[F[3]][len(base[F[3]]):]
    p += [f"--base phrase {d} changed without a LEDGER line" for d in changed if d.split(".")[-1] not in led]
    return p, changed


def copy(dst):
    for d in ("scripts", "runs"):
        shutil.copytree(os.path.join(tree, d), os.path.join(dst, d))
    shutil.copy(os.path.join(tree, "LEDGER.md"), dst)


tmp = tempfile.mkdtemp(); copy(tmp)
c, _ = problems(tmp)
print(f"control (unmodified tree): {len(c)} problems" + "".join("\n    " + x[:300] for x in c))
shutil.rmtree(tmp)
for dd in sys.argv[2:]:
    tmp = tempfile.mkdtemp(); copy(tmp)
    name = os.path.basename(dd.rstrip("/"))
    r = subprocess.run([sys.executable, os.path.join(dd, "apply.py"), tmp], capture_output=True, text=True)
    if r.returncode:
        gen = [l for l in r.stdout.splitlines() if "(P1" in l]
        if gen and "write_generated() == 0" in r.stderr:
            print(f"{name}: REJECTED (the defect's own `check_claims.py --generate` step refuses to generate):")
            for l in gen:
                print("    " + l[:300])
        else:
            print(f"{name}: apply.py FAILED on this tree: {(r.stderr.strip().splitlines() or [''])[-1][:300]}")
        shutil.rmtree(tmp); continue
    p, changed = problems(tmp)
    print(f"{name}: phrases changed {changed} -> {'REJECTED' if p else 'passes the phrase rules'}")
    for h in p:
        print("    " + h[:300])
    shutil.rmtree(tmp)
