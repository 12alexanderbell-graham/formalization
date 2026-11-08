"""Run 2026-11-08T2028Z: generic row porter (from port_k.py, which did K = 5). Ports the Homann (coefficient 2) stack to an
integer coefficient K, i.e. the scaled Falkner-Skan beta = 1/K problem f''' + 5 f f'' + 1 - f'^2 = 0 (F(s) = c f(s/c), c = sqrt(beta), maps the
Falkner-Skan equation f''' + f f'' + beta (1 - f'^2) = 0 to F''' + (1/beta) F F'' + 1 - F'^2 = 0).
Text substitution of every K-dependent token (found by diffing Work/Hiemenz against Work/Homann); after the
run, every remaining '2 *' in the outputs is listed for review.
usage: port_row.py K NS P LO HI H   e.g. 10 FSTenth F10 1.8563683593 1.8563683595 3
(writes Work/<NS>/<P>*.lean, Work/<NS>/<NS>.lean and runs/2026-11-08T2028Z/scripts/emit_k<K>_{w,wc}.py)"""
import re, sys, os
KK, NS, P, LO, HI, H = sys.argv[1:7]
k = int(KK)
os.makedirs("Work/%s" % NS, exist_ok=True)
R = 'runs/2026-11-08T2028Z/scripts/'
mods = {'HmExBase': '' + P + 'ExBase', 'HmExFlow': '' + P + 'ExFlow', 'HmExLimit': '' + P + 'ExLimit', 'HmExAssemble': '' + P + 'ExAssemble',
        'HmCellWC': '' + P + 'CellWC', 'HmCellW': '' + P + 'CellW', 'HmUDataC': '' + P + 'UDataC', 'HmODataC': '' + P + 'ODataC',
        'HmUData': '' + P + 'UData', 'HmOData': '' + P + 'OData', 'HmExMono': '' + P + 'ExMono', 'HmIVP': '' + P + 'IVP'}
K = [('-(2 * ', '-(%d * ' % k), ('(2 * mlo c', '(%d * mlo c' % k), ('2 * qlo c', '%d * qlo c' % k), ('2 * qhi c', '%d * qhi c' % k),
     ('2 * P3', '%d * P3' % k), ('2 * y1', '%d * y1' % k), ('2 * P1', '%d * P1' % k), ('2 * evalQ c.pg', '%d * evalQ c.pg' % k),
     ('2 * evalQ c.pq', '%d * evalQ c.pq' % k), ('|2 * cl C', '|%d * cl C' % k), ('≤ 2 * C * 2', '≤ %d * C * 2' % k),
     ('2 * T + 12', '%d * T + %d' % (k, 4 * k + 4)), ('4 * T + 13', '%d * T + %d' % (2 * k, 4 * k + 5)),
     ('abs_two', 'abs_of_pos (by norm_num : (0 : ℝ) < %d)' % k),
     ('(qmul (qadd c.pg c.pg) c.pq)', '(qmul (qsmul %d c.pg) c.pq)' % k),
     ('evalQ_qmul, ← dEvalQ_eq]', 'evalQ_qmul, evalQ_qsmul, ← dEvalQ_eq]'),
     ('1.3119376938', LO), ('1.3119376939', HI),
     ('−2 g q', '−%d g q' % k), ('−2 f q', '−%d f q' % k), ("2 g g''", "%d g g''" % k), ("2 f f''", "%d f f''" % k), ('2·pg·pq', '%d·pg·pq' % k),
     ('(2 y1 − m)', '(%d y1 − m)' % k), ('(2 P3, s) and m = 2 mlo', '(%d P3, s) and m = %d mlo' % (k, k)),
     ('(2 P3 ∈ {2 qlo, 2 qhi}', '(%d P3 ∈ {%d qlo, %d qhi}' % (k, k, k)),
     ('os_homann', 'os_k%d' % k)]
def port(s, extra=()):
    for a, b in mods.items():
        s = re.sub(r'(Work|Checked)\.Homann\.' + a + r'\b', 'Work.' + NS + '.' + b, s)
    s = s.replace('namespace Work.Homann', 'namespace Work.' + NS).replace('end Work.Homann', 'end Work.' + NS)
    s = s.replace('namespace Checked.Homann', 'namespace Work.' + NS).replace('end Checked.Homann', 'end Work.' + NS)
    s = s.replace('Work.Homann.homann_', 'Work.' + NS + '.k%d_' % k).replace('Checked.Homann.homann_', 'Work.' + NS + '.k%d_' % k)
    for a, b in K: s = s.replace(a, b)
    for a, b, n in extra:
        c = s.count(a); assert c == n, (a, c, n); s = s.replace(a, b)
    s = s.replace('Homann axisymmetric stagnation-point flow', 'Falkner–Skan β = 1/%d in scaled form (coefficient %d)' % (k, k))
    s = s.replace('the Homann field', 'the coefficient-%d field' % k).replace('Homann', 'K = %d (Falkner–Skan β = 1/%d, scaled)' % (k, k))
    return s
H6 = [('Icc (0 : ℝ) 6', 'Icc (0 : ℝ) ' + H), ('Icc 0 6', 'Icc 0 ' + H)]
out = {}
for m in ['HmExBase', 'HmExFlow', 'HmExLimit', 'HmCellW', 'HmCellWC']:
    out[mods[m]] = port(open('Work/Homann/%s.lean' % m).read())
s = open('Work/Homann/HmExAssemble.lean').read()
out['' + P + 'ExAssemble'] = port(s, [(a, b, s.count(a)) for a, b in H6])
s = open('Checked/Homann/HmExMono.lean').read()
out['' + P + 'ExMono'] = port(s)
s = open('Checked/Homann/HmIVP.lean').read()
out['' + P + 'IVP'] = port(s)
for kk, v in out.items():
    v = re.sub(r'^(import Mathlib\.[^\n]*\n)+', 'import Mathlib\n', v, flags=re.M) if not v.startswith('import Mathlib\n') else v
    open('Work/%s/%s.lean' % (NS, kk), 'w').write(v)
# emitters
for src, dst in [('emit_homann_w.py', 'emit_k%d_w.py' % k), ('emit_homann_wc.py', 'emit_k%d_wc.py' % k)]:
    s = open('runs/2026-11-08T0428Z/scripts/' + src).read()
    s = s.replace('runs/2026-11-08T0428Z/scripts/gen_homann_w.py', 'runs/2026-11-08T2028Z/scripts/gen_k_w.py (FS_K = 5)')
    s = s.replace('runs/2026-11-08T0428Z/scripts/gen_homann_wc.py', 'runs/2026-11-08T2028Z/scripts/gen_k_wc.py (FS_K = 5)')
    s = s.replace('emit_homann_wc.py', 'emit_k%d_wc.py' % k).replace('emit_homann_w.py', 'emit_k%d_w.py' % k)
    s = port(s)
    open(R + dst, 'w').write(s)
print('ok')
