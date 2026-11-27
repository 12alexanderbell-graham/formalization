#!/usr/bin/env python3
"""Map every paper of OpenAI's release to ALL its comparator challenges and its scope document
(run 2026-11-27T1248Z; PROMPT 11, "Target O correction").

  python3 scripts/external/family_map.py <openai/math clone> [--challenge NAME ...] [--doc NNN ...] [--check]

Why: run 2026-11-27T0628Z mapped families to challenges first by size order and then by solution directory
(`family_challenges.py`); both missed challenges (O20, O21 findings wrong and withdrawn) and neither read
OpenAI's own statement of what the Lean covers. At the release pin (3344da5) `lean/formalization.yaml` lists
the papers (`sources`, id = paper path) and the challenges (`status.main_results`, by comparator config), but
no main_result names its paper. The paper <-> challenge link is in the scope documents `lean/docs/NNN.md`
(linked from `CONTENTS.md` as "([Lean](lean/docs/NNN.md))"): each names its paper(s) by the same path as the
yaml `sources` ids and lists its challenges under "## Comparator links". This script reads those links, so
a family is the set of challenges of its scope document, whatever their names or directories.

Output per document: number, title, paper path(s) (checked against yaml `sources`), every challenge (checked
to exist as `ComparatorChallenges/<name>.json`), and the scope text's sentences that limit coverage
("only", "does not", "outside", "not formalized", ...), which are the DISCLOSED gaps.
--contents: compare every CONTENTS.md item that carries a "[Lean]" link with its scope document: list the item's
papers that the document does not cover, and flag (INDEX-HEADLINE) an item whose document title is closer to an
uncovered paper's title than to every covered one: the index then presents, under the Lean link, a claim from a
paper the Lean does not formalize (found on item 197, torsion-free over F_2, and 084, every ratio q, by run
2026-11-27T1248Z). A flag is a lead, not a verdict: read the item, the scope text and the challenges.
--check: also report challenges no document links, documents whose paper is not a yaml source, and challenges
linked from more than one document.
"""
import glob
import json
import os
import re
import sys

LIMIT = re.compile(r"\b(only|does not|do not|not (?:formali[sz]ed|asserted|included|covered|claimed|part)|outside|"
                   r"omit|omitted|excluded|exclud|beyond|not this|left|rather than|instead of|weaker|special case|"
                   r"partial|restricted|restrict|unformali[sz]ed|not separately|not addressed|not covered)\b", re.I)


def parse_doc(path):
    txt = open(path, encoding='utf-8').read()
    num = os.path.basename(path)[:-3]
    title = txt.splitlines()[0].lstrip('# ').strip()
    papers = re.findall(r'\]\(\.\./\.\./(preprints/[^)]+)\)', txt.split('## Scope')[0])
    scope = txt.split('## Scope', 1)[1].split('## Comparator links', 1)[0].strip() if '## Scope' in txt else ''
    links = txt.split('## Comparator links', 1)[1] if '## Comparator links' in txt else ''
    rows = []
    for line in links.splitlines():
        m = re.match(r'\|\s*(.*?)\s*\|\s*(.*)\|\s*$', line)
        if not m or set(m.group(1)) <= set('-: '):
            continue
        chals = re.findall(r'ComparatorChallenges/([A-Za-z0-9_]+)\.lean', m.group(2))
        if chals:
            rows.append((m.group(1), chals))
    sentences = [s.strip() for s in re.split(r'(?<=[.;])\s+', scope.replace('\n', ' ')) if LIMIT.search(s)]
    return dict(num=num, title=title, papers=papers, scope=scope, rows=rows, limits=sentences)


def main():
    root = sys.argv[1]
    args = sys.argv[2:]
    want_c = [args[i + 1] for i, a in enumerate(args) if a == '--challenge']
    want_d = [args[i + 1] for i, a in enumerate(args) if a == '--doc']
    lean = os.path.join(root, 'lean')
    docs = [parse_doc(p) for p in sorted(glob.glob(os.path.join(lean, 'docs', '*.md')))]
    yaml = open(os.path.join(lean, 'formalization.yaml'), encoding='utf-8').read()
    sources = set(re.findall(r'id:\s*\.\./(preprints/\S+)', yaml))
    allc = {os.path.basename(f)[:-5] for f in glob.glob(os.path.join(lean, 'ComparatorChallenges', '*.json'))}
    sel = docs
    if want_c or want_d:
        sel = [d for d in docs if d['num'] in want_d or any(c in want_c for _, cs in d['rows'] for c in cs)]
    for d in sel:
        print('== %s  %s' % (d['num'], d['title']))
        for p in d['papers']:
            print('   paper: %s%s' % (p, '' if p in sources else '   [NOT a formalization.yaml source]'))
        for res, cs in d['rows']:
            for c in cs:
                n = sum(1 for _ in open(os.path.join(lean, 'ComparatorChallenges', c + '.lean'))) \
                    if c in allc else -1
                th = ' '.join(json.load(open(os.path.join(lean, 'ComparatorChallenges', c + '.json')))['theorem_names']) \
                    if c in allc else 'MISSING'
                print('   challenge %-34s %4d lines  %s\n             result: %s' % (c, n, th, res[:160]))
        for s in d['limits']:
            print('   DISCLOSED: %s' % s[:400])
    if '--check' in args:
        linked = {}
        for d in docs:
            for _, cs in d['rows']:
                for c in cs:
                    linked.setdefault(c, set()).add(d['num'])
        print('# %d documents, %d challenges, %d linked' % (len(docs), len(allc), len(set(linked) & allc)))
        for c in sorted(allc - set(linked)):
            print('# UNLINKED challenge: %s' % c)
        for c, ds in sorted(linked.items()):
            if len(ds) > 1:
                print('# challenge in several documents: %s %s' % (c, sorted(ds)))
            if c not in allc:
                print('# linked but no json: %s %s' % (c, sorted(ds)))
        for d in docs:
            if not d['papers'] or any(p not in sources for p in d['papers']):
                print('# document %s: paper not among formalization.yaml sources: %s' % (d['num'], d['papers']))


def contents_check(root):
    import difflib
    txt = open(os.path.join(root, 'CONTENTS.md'), encoding='utf-8').read()
    norm = lambda t: re.sub(r'[^a-z0-9 ]', ' ', t.lower().replace('-', ' '))
    ptitle = lambda path: os.path.dirname(path)[len('preprints/'):].rsplit('-', 3)[0].replace('-', ' ')
    n = 0
    for part in re.split(r'\n(?=\*\*\d{3}\. )', txt):
        m = re.match(r'\*\*(\d{3})\. (.*?)\*\*', part)
        lean = m and re.search(r'\(\[Lean\]\(lean/docs/(\d{3})\.md\)\)', part.split('\n')[0])
        if not lean:
            continue
        n += 1
        d = parse_doc(os.path.join(root, 'lean', 'docs', lean.group(1) + '.md'))
        papers = re.findall(r'\]\((preprints/[^)]+)\)', part)
        extra = [p for p in papers if p not in d['papers']]
        if not extra:
            continue
        sim = lambda p: difflib.SequenceMatcher(None, norm(d['title']), norm(ptitle(p))).ratio()
        best_cov = max([sim(p) for p in d['papers']] or [0])
        best_ext = max(extra, key=sim)
        flag = 'INDEX-HEADLINE ' if sim(best_ext) > best_cov and sim(best_ext) > 0.6 else ''
        print('%sitem %s (doc %s "%s"): uncovered papers: %s' % (flag, m.group(1), d['num'], d['title'],
              '; '.join(ptitle(p) for p in extra)))
    print('# %d CONTENTS items with a Lean link' % n)


if __name__ == '__main__':
    if '--contents' in sys.argv:
        contents_check(sys.argv[1])
        sys.exit(0)
    main()
