"""Rewrite scripts/trust/necessity_open_baseline.txt from TRUST_MAP.md (check_necessity N1: the baseline lists
exactly the open indices). Keeps the header comment lines. Run after StatementDeps."""
import re
tm = open('TRUST_MAP.md', encoding='utf-8').read().splitlines()
lines = []
for l in tm:
    m = re.match(r"^- `([^`]+)` \((\d+)\): (.*)$", l)
    if not m:
        continue
    rest = m.group(3).split('; shape:')[0]
    o = re.search(r"(?:^|; )open ([\d, ]+)$", rest.strip())
    if o:
        lines.append(f"{m.group(1)} | {o.group(1).strip()}")
p = 'scripts/trust/necessity_open_baseline.txt'
head = [l for l in open(p, encoding='utf-8').read().splitlines() if l.startswith('#')]
old = [l for l in open(p, encoding='utf-8').read().splitlines() if l and not l.startswith('#')]
new = {l.split(' | ')[0]: l for l in lines}
ordered = [new[o.split(' | ')[0]] for o in old if o.split(' | ')[0] in new]
ordered += [l for l in lines if l not in ordered]
open(p, 'w', encoding='utf-8').write('\n'.join(head + ordered) + '\n')
print(f'baseline: {len(old)} -> {len(lines)} lines')
