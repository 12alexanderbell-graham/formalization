#!/usr/bin/env python3
"""Planted controls for the P3 route check (`check_claims.roles_route`, run 2026-11-08T2228Z) and P12
(`baseline_reentry`), run 2026-11-09T1428Z (STATE exact next step 2: 'a planted control for the P3 route check').
Builds scratch git repositories from this checkout's scripts/trust and registry and replays commit sequences:
  good   brief alone -> reading alone -> registry copy                     : route passes
  same   brief + reading + registry copy in ONE commit                     : must fail
  early  brief alone -> registry copy -> reading                           : must fail (registry before the reading)
  wide   brief alone -> reading together with a scripts/ change -> copy    : must fail (reading commit outside runs/<run>/)
  rejoin an excluded baseline line moved into the registry in one commit   : must fail (P12)
  fb17*  the same sequences for a class phrase of check_findings.py FB17 (b) (run 2026-11-14T1228Z), plus a brief
         that contains the phrase (leak) and a registry line with no reading at all (none): only fb17good passes
usage: route_control.py   (exit 1 if any control misbehaves)"""
import os, shutil, subprocess, sys, tempfile
SRC = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
R = "scripts/trust/phrase_roles.txt"
RUN = "runs/2099-01-01T0000Z/shapes9"
LINE = "SHAPE | Checked.Sim.Duffing.IsDuffingSolution | property | x | is | the"  # a line not yet in the registry


def sh(cwd, *a):
    return subprocess.run(a, cwd=cwd, capture_output=True, text=True)


def repo():
    d = tempfile.mkdtemp()
    shutil.copytree(os.path.join(SRC, "scripts"), os.path.join(d, "scripts"))
    shutil.copytree(os.path.join(SRC, "runs"), os.path.join(d, "runs"))
    for f in ("LEDGER.md",):
        shutil.copy(os.path.join(SRC, f), d)
    sh(d, "git", "init", "-q"); sh(d, "git", "config", "user.email", "c@x"); sh(d, "git", "config", "user.name", "c")
    sh(d, "git", "add", "-A"); sh(d, "git", "commit", "-qm", "base")
    return d, sh(d, "git", "rev-parse", "HEAD").stdout.strip()


def write(d, p, t, append=False):
    os.makedirs(os.path.dirname(os.path.join(d, p)), exist_ok=True)
    with open(os.path.join(d, p), "a" if append else "w", encoding="utf-8") as f:
        f.write(t)


def commit(d, *paths):
    sh(d, "git", "add", *paths); sh(d, "git", "commit", "-qm", "c")


def brief(d): write(d, RUN + "/BRIEF.md", "brief\n")
def reading(d): write(d, RUN + "/SHAPES.txt", LINE + "\nEND\n")
def copy(d): write(d, R, f"# source: {RUN}/SHAPES.txt\n{LINE}\n", append=True)


def route(d, base):
    code = ("import sys; sys.path.insert(0,'scripts/trust'); import check_claims as cc; "
            f"print(len(cc.roles_route('{base}')), len(cc.baseline_reentry('{base}')))")
    out = sh(d, sys.executable, "-c", code)
    return tuple(int(x) for x in out.stdout.split()) if out.returncode == 0 else (None, out.stderr)


cases = {}
d, b = repo(); brief(d); commit(d, RUN); reading(d); commit(d, RUN); copy(d); commit(d, R); cases["good"] = (route(d, b), False)
d, b = repo(); brief(d); reading(d); copy(d); commit(d, RUN, R); cases["same"] = (route(d, b), True)
d, b = repo(); brief(d); commit(d, RUN); copy(d); commit(d, R); reading(d); commit(d, RUN); cases["early"] = (route(d, b), True)
d, b = repo(); brief(d); commit(d, RUN); reading(d); write(d, "scripts/x.txt", "x\n"); commit(d, RUN, "scripts/x.txt")
copy(d); commit(d, R); cases["wide"] = (route(d, b), True)
d, b = repo()
line = "CLAUSE | Checked.Chemistry.Coexistence.IsMaxwellCoexistence | equivalent to equal chemical potential in both phases"
bp = os.path.join(d, "scripts/trust/phrase_clause_baseline.txt")
t = open(bp, encoding="utf-8").read(); open(bp, "w", encoding="utf-8").write(t.replace(line + "\n", ""))
rp = os.path.join(d, R)
t = open(rp, encoding="utf-8").read()
a = "CLAUSE | Checked.Chemistry.Coexistence.IsMaxwellCoexistence | equal areas between the isotherm and the saturation pressure line\n"
open(rp, "w", encoding="utf-8").write(t.replace(a, a + line + "\n"))
commit(d, "scripts"); r = route(d, b); cases["rejoin"] = ((r[0], r[1]), "p12")

# FB17 (b) of check_findings.py (run 2026-11-14T1228Z, blind round AO d01, d03): a class phrase added to the registry
# is a verbatim copy of a blind reading runs/<run>/<dir>/class_phrases_reading*.txt (brief -> reading -> copy)
FR = "scripts/trust/finding_class_phrases.txt"
FRUN = "runs/2099-01-01T0000Z/classes1"
FLINE = "`Filter.Tendsto p Filter.atTop (nhds 1)` => far-field velocity one"


def fbrief(d, leak=False): write(d, FRUN + "/brief.md", "brief" + (" far-field velocity one" if leak else "") + "\n")
def freading(d): write(d, FRUN + "/class_phrases_reading.txt", FLINE + "\n")
def fcopy(d): write(d, FR, FLINE + "\n", append=True)


def froute(d, base):
    code = ("import sys, subprocess; sys.path.insert(0,'scripts/trust'); import check_findings as cf; "
            f"old = subprocess.run(['git','show','{base}:{FR}'],capture_output=True,text=True).stdout; "
            "newp = sorted(set(cf.load_phrases()) - set(cf.load_phrases(text=old))); "
            "print(len(cf.fb17_route(newp, cf.class_phrase_readings())), 0)")
    out = sh(d, sys.executable, "-c", code)
    return tuple(int(x) for x in out.stdout.split()) if out.returncode == 0 else (None, out.stderr)


d, b = repo(); fbrief(d); commit(d, FRUN); freading(d); commit(d, FRUN); fcopy(d); commit(d, FR); cases["fb17good"] = (froute(d, b), False)
d, b = repo(); fbrief(d); freading(d); fcopy(d); commit(d, FRUN, FR); cases["fb17same"] = (froute(d, b), True)
d, b = repo(); fbrief(d); commit(d, FRUN); fcopy(d); commit(d, FR); freading(d); commit(d, FRUN); cases["fb17early"] = (froute(d, b), True)
d, b = repo(); fbrief(d); commit(d, FRUN); freading(d); write(d, "scripts/x.txt", "x\n"); commit(d, FRUN, "scripts/x.txt")
fcopy(d); commit(d, FR); cases["fb17wide"] = (froute(d, b), True)
d, b = repo(); fbrief(d, leak=True); commit(d, FRUN); freading(d); commit(d, FRUN); fcopy(d); commit(d, FR); cases["fb17leak"] = (froute(d, b), True)
d, b = repo(); fcopy(d); commit(d, FR); cases["fb17none"] = (froute(d, b), True)

bad = 0
for k, (r, must_fail) in cases.items():
    if must_fail == "p12":
        ok = r[1] == 1
    else:
        ok = r[0] is not None and ((r[0] > 0) == must_fail)
    print(f"{k:7s} route problems {r[0]}, P12 problems {r[1]} -> {'ok' if ok else 'CONTROL FAILED'}")
    bad += not ok
sys.exit(1 if bad else 0)
