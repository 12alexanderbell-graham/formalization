"""Fast local pre-check (no Lean) of the StatementDeps records rule: every backticked token in
STATE.md / FINDINGS.md that names a Checked theorem (full name or dotted suffix) must be a
registered headline (scripts/trust/headlines.txt). Approximates the Lean check (namespaces from
`namespace` lines; the Lean check exempts pure-mathematics lemmas, so a hit here may be a false
alarm). Run before every records commit (run 2026-11-06T0828Z: the records commit of run 0628Z cited
a pin theorem and an NV witness by name; the trust step on main was red for two hours).
Usage: python3 scripts/trust/precheck_citations.py  (exit 1 on a suspected violation)"""
import os, re, glob, sys

thms = set()
decls = set()
for f in glob.glob('Checked/**/*.lean', recursive=True):
    ns = []
    inprop = None
    for line in open(f, encoding='utf-8'):
        m = re.match(r'\s*namespace\s+(\S+)', line)
        if m: ns.append(m.group(1)); continue
        m = re.match(r'\s*end\s+(\S+)', line)
        if m and ns and ns[-1] == m.group(1): ns.pop(); continue
        md = re.match(r'\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque)\s+([^\s:({\[]+)', line)
        if md:
            nm = md.group(1)
            decls.add(nm if nm.startswith('Checked.') else '.'.join(ns + [nm]))
        # fields of a `structure … : Prop` are theorems too (run 2026-11-07T0028Z: STATE.md backticked `deriv`,
        # which the Lean check resolved to the field `Checked.Math.TFExAssemble.Sol.deriv`; the trust step on
        # main was red from 5ec9b9a while this script reported 0)
        ms = re.match(r'\s*structure\s+([^\s:({\[]+).*:\s*Prop\s+where', line)
        if ms:
            inprop = '.'.join(ns + [ms.group(1)]); continue
        if inprop:
            mf = re.match(r'\s+([^\s:({\[]+)\s*:', line)
            if mf and not line.lstrip().startswith('--'):
                # «open»-quoted field names are the constant `….open` (run 2026-11-11T1028Z: STATE.md backticked
                # `open`, the Lean check resolved it to `Checked.Fidelity.AngDistSpec.open`, this script reported 0)
                fld = mf.group(1).strip('«»')
                thms.add(inprop + '.' + fld); decls.add(inprop + '.' + fld); continue
            if not line.strip() or not line[0].isspace():
                inprop = None
        m = re.match(r'\s*(?:private\s+)?(?:theorem|lemma)\s+(\S+)', line)
        if m:
            nm = m.group(1)
            full = nm if nm.startswith('Checked.') else '.'.join(ns + [nm])
            thms.add(full)
heads = [l.strip() for l in open('scripts/trust/headlines.txt', encoding='utf-8')
         if l.strip() and not l.startswith('#')]
def is_head(t):
    return any(t == h or t.endswith('.' + h) or h.endswith('.' + t.split('.')[-1]) and (t == h or h.endswith('.' + t) or t.endswith('.' + h)) for h in heads)
text = open('STATE.md', encoding='utf-8').read() + '\n' + open('FINDINGS.md', encoding='utf-8').read()
toks = [t for i, t in enumerate(text.split('`')) if i % 2 == 1 and t and ' ' not in t]
bad = set()
for t in toks:
    variants = [t]
    m = re.match(r'^(.*)\[(.*)\](.*)$', t)
    if m: variants = [m.group(1) + m.group(3), m.group(1) + m.group(2) + m.group(3)]
    for v in variants:
        hits = [n for n in thms if n == v or n.endswith('.' + v)]
        if len(hits) == 1:
            n = hits[0]
            if not any(n == h or n.endswith('.' + h) for h in heads):
                bad.add(n)
# The Lean check also rejects a backticked `Checked.…` token that names no constant (a module or
# namespace name such as `Checked.Sim.MMCerts`; run 2026-11-06T1828Z: the 1428Z records commit cited
# a module this way and the trust step on main was red from 04feda9 until the repair).
for t in toks:
    if t.startswith('Checked.') and '/' not in t and not re.search(r'[\[\]]', t):
        tt = t.rstrip('.,;:')
        if tt not in decls and not any(d.endswith('.' + tt) for d in decls):
            bad.add(tt + ' (no such constant: module or namespace name?)')
# pure-mathematics lemmas (no program definition in the statement): exempt in the Lean check too
PURE = {'Checked.Cosmography.BambaY.littleO_of_hasDerivAt', 'Checked.Math.LECell.tube_cell_t',
        'Checked.Sim.OneSided.onesided_cell'}
bad -= PURE
# agreement theorems of Checked.Trust.Transcriptions: exempt in the Lean check too (run 2026-11-13T2028Z; every
# theorem there is a checked blind-reading agreement or a blocking error; run 1828Z's generated Printed lines cite them)
bad = {n for n in bad if not n.startswith('Checked.Trust.Transcriptions.')}
for n in sorted(bad):
    print(f'suspected: STATE.md/FINDINGS.md cite {n}, which is not in scripts/trust/headlines.txt')
print(f'precheck_citations: {len(bad)} suspected')
# Records commits also break the status-line rule (check_status_lines S1-S3 reads STATE.md against CLAIMS.md):
# 1727c31 (run 2026-11-11T2228Z) put 'global' into a STATE status line and turned the checked job's trust step
# red although every Lean and necessity check passed. It is pure Python (< 1 s), so the records precheck runs
# it too (run 2026-11-12T0227Z, LEDGER); a records commit then needs only this one command.
import subprocess
here = os.path.dirname(os.path.abspath(__file__))
rc = subprocess.call([sys.executable, os.path.join(here, 'check_status_lines.py')])
sys.exit(1 if (bad or rc) else 0)
