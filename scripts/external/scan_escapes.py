#!/usr/bin/env python3
"""Scan the import closure of an outside Lean module for trust escapes (external test, standing
instruction 11; run 2026-11-26T1529Z). General: works on any Lake project tree, not only ours.

  python3 scripts/external/scan_escapes.py <project root> <Module.Name> [<Module.Name> ...]

Reports, per file of the closure inside the project (imports that resolve outside it, e.g. Mathlib,
are listed by package and not scanned), every occurrence of:
  sorry / admit                      unfinished proof
  axiom                              new axiom (kernel accepts it unchecked)
  native_decide / ofReduceBool / Lean.trustCompiler   compiler-trusted evaluation
  implemented_by / extern            runtime code replacing a definition
  unsafe / opaque / partial          definitions the kernel cannot unfold
  set_option debug. / maxRecDepth    kernel or elaborator switches
  macro / elab / syntax / notation   custom syntax (can make a statement read differently than it elaborates)
  #exit                              stops checking the rest of the file
The scan is advisory: the binding checks are `#print axioms` on the headline (only propext,
Classical.choice, Quot.sound) and an independent kernel replay. A hit is a place to read, not a verdict.
Comments and strings are stripped before matching.
"""
import os
import re
import sys
from collections import Counter

PATTERNS = {
    'sorry': r'\bsorry\b|\badmit\b',
    'axiom': r'^\s*(?:private\s+|protected\s+)?axiom\b',
    'native': r'\bnative_decide\b|\bofReduceBool\b|\btrustCompiler\b',
    'implemented_by': r'\bimplemented_by\b|@\[extern\b|\bextern\b',
    'unsafe/opaque/partial': r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(?:unsafe|opaque|partial)\b',
    'set_option debug/kernel': r'set_option\s+(?:debug\.|maxRecDepth|backward\.)',
    'custom syntax': r'^\s*(?:@\[[^\]]*\]\s*)?(?:scoped\s+|local\s+)?(?:macro|elab|syntax|notation|infix|infixl|infixr|prefix|postfix|macro_rules|elab_rules)\b',
    '#exit': r'^\s*#exit\b',
}


def strip(src):
    """Remove comments (Lean block comments NEST: `/- a /- b -/ c -/` is one comment; a non-nesting
    regex left the tail of a docstring as code and reported its example `axiom` lines, run
    2026-11-26T1529Z, zeta-23 AdditiveCombination.lean) and string literals; keep line numbers."""
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if src.startswith('/-', i):
            depth += 1; i += 2; continue
        if depth and src.startswith('-/', i):
            depth -= 1; i += 2; continue
        if depth:
            if src[i] == '\n':
                out.append('\n')
            i += 1; continue
        if src.startswith('--', i):
            j = src.find('\n', i)
            i = n if j < 0 else j
            continue
        if src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == '\\' else 1
            out.append('""'); i = j + 1; continue
        out.append(src[i]); i += 1
    return ''.join(out)


def closure(root, mods):
    seen, ext = {}, Counter()

    def go(m):
        if m in seen:
            return
        p = os.path.join(root, m.replace('.', '/') + '.lean')
        if not os.path.exists(p):
            ext[m.split('.')[0]] += 1
            return
        seen[m] = p
        for line in open(p, encoding='utf-8'):
            mm = re.match(r'\s*(?:public\s+)?(?:meta\s+)?import\s+(.*)', line)
            if mm:
                for x in mm.group(1).split():
                    go(x)
    for m in mods:
        go(m)
    return seen, ext


def main():
    root, mods = sys.argv[1], sys.argv[2:]
    seen, ext = closure(root, mods)
    nlines = 0
    hits = Counter()
    for m, p in sorted(seen.items()):
        src = strip(open(p, encoding='utf-8').read())
        nlines += src.count('\n')
        for i, line in enumerate(src.split('\n'), 1):
            for k, pat in PATTERNS.items():
                if re.search(pat, line):
                    hits[k] += 1
                    print(f'{k}\t{os.path.relpath(p, root)}:{i}\t{line.strip()[:120]}')
    print(f'# closure: {len(seen)} files, {nlines} lines; external packages: {dict(ext)}')
    print('# hits: ' + (', '.join(f'{k} {v}' for k, v in sorted(hits.items())) or 'none'))


if __name__ == '__main__':
    main()
