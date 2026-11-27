#!/usr/bin/env python3
"""Readings.lean from the blind reader files, code unchanged, each wrapped in `namespace Reader<X>`
(run 2026-11-27T0628Z, target O, quasi-RH family). python3 mk_readings.py <family dir>"""
import os, sys
D = sys.argv[1]
out = ['import Mathlib', '']
for r in 'ABC':
    src = open(os.path.join(D, r, 'reading.lean'), encoding='utf-8').read()
    body = src.split('\n', 1)[1] if src.startswith('import Mathlib') else src
    # a reader file may leave an anonymous `section` open at its end (legal at end of file);
    # close it before the wrapper's namespace ends
    import re
    opened = len(re.findall(r'^\s*(?:noncomputable\s+)?section\s*$', body, flags=re.M))
    closed = len(re.findall(r'^\s*end\s*$', body, flags=re.M))
    out += [f'namespace Reader{r}', body.rstrip('\n')] + ['end'] * max(0, opened - closed) + [f'end Reader{r}', '']
open(os.path.join(D, 'closure', 'Readings.lean'), 'w', encoding='utf-8').write('\n'.join(out))
print('ok')
