"""Fast local pre-check (no Lean) of the StatementDeps records rule: every backticked token in
STATE.md / FINDINGS.md that names a Checked theorem (full name or dotted suffix) must be a
registered headline (scripts/trust/headlines.txt). Approximates the Lean check (namespaces from
`namespace` lines; the Lean check exempts pure-mathematics lemmas, so a hit here may be a false
alarm). Run before every records commit (run 2026-11-06T0828Z: the records commit of run 0628Z cited
a pin theorem and an NV witness by name; the trust step on main was red for two hours).
Usage: python3 scripts/trust/precheck_citations.py  (exit 1 on a suspected violation)"""
import re, glob, sys

thms = set()
for f in glob.glob('Checked/**/*.lean', recursive=True):
    ns = []
    for line in open(f, encoding='utf-8'):
        m = re.match(r'\s*namespace\s+(\S+)', line)
        if m: ns.append(m.group(1)); continue
        m = re.match(r'\s*end\s+(\S+)', line)
        if m and ns and ns[-1] == m.group(1): ns.pop(); continue
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
# pure-mathematics lemmas (no program definition in the statement): exempt in the Lean check too
PURE = {'Checked.Cosmography.BambaY.littleO_of_hasDerivAt', 'Checked.Math.LECell.tube_cell_t',
        'Checked.Sim.OneSided.onesided_cell'}
bad -= PURE
for n in sorted(bad):
    print(f'suspected: STATE.md/FINDINGS.md cite {n}, which is not in scripts/trust/headlines.txt')
print(f'precheck_citations: {len(bad)} suspected')
sys.exit(1 if bad else 0)
