"""Prototype of P7: every token of a phrase is covered by a blind text (NAME, ROLE before its placeholder, SIGN) or is a connective."""
import re, sys
sys.path.insert(0, "scripts/trust")
import check_claims as cc
TOK = re.compile(r"[^\W_]+(?:['’][A-Za-z]+)?|[{][^}]*[}]")
CONN = set("the a an of at for in on with and or by from to".split())
phr = cc.parse_phrases(open(cc.PHR, encoding="utf-8").read())
roles, signs, bad = cc.load_roles()
tot = 0
for d, p in sorted(phr.items()):
    key = cc._full(d, roles) or cc._full(d, signs)
    toks = [t.lower() for t in TOK.findall(p)]
    cov = [False] * len(toks)
    texts = []
    rmap = roles.get(key, {}) if key else {}
    for x, r in rmap.items():
        texts.append([w.lower() for w in TOK.findall(r)] + ["{" + x.lower() + "}"])
    for c in (signs.get(key, []) if key else []):
        texts.append([w.lower() for w in TOK.findall(c)])
    for t in texts:
        n = len(t)
        for i in range(len(toks) - n + 1):
            if toks[i:i + n] == t:
                for j in range(i, i + n): cov[j] = True
    for i, t in enumerate(toks):
        if t.startswith("{"): cov[i] = True  # later occurrences of a placeholder
    unc = [t for t, c in zip(toks, cov) if not c and t not in CONN]
    if unc:
        tot += 1
        print(f"{d}: {' '.join(unc)}")
print("phrases with uncovered words:", tot, "of", len(phr))
