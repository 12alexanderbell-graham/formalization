"""Run 2026-11-08T2028Z: port the Homann (coefficient K = 2) stack to the coefficient K = 5, i.e. the scaled
Falkner-Skan beta = 1/5 problem f''' + 5 f f'' + 1 - f'^2 = 0 (F(s) = c f(s/c), c = sqrt(beta), maps the
Falkner-Skan equation f''' + f f'' + beta (1 - f'^2) = 0 to F''' + (1/beta) F F'' + 1 - F'^2 = 0).
Text substitution of every K-dependent token (found by diffing Work/Hiemenz against Work/Homann); after the
run, every remaining '2 *' in the outputs is listed for review.
usage: port_k.py  (writes Work/FSFifth/*.lean and runs/2026-11-08T2028Z/scripts/emit_k5_{w,wc}.py)"""
import re
R = 'runs/2026-11-08T2028Z/scripts/'
mods = {'HmExBase': 'F5ExBase', 'HmExFlow': 'F5ExFlow', 'HmExLimit': 'F5ExLimit', 'HmExAssemble': 'F5ExAssemble',
        'HmCellWC': 'F5CellWC', 'HmCellW': 'F5CellW', 'HmUDataC': 'F5UDataC', 'HmODataC': 'F5ODataC',
        'HmUData': 'F5UData', 'HmOData': 'F5OData', 'HmExMono': 'F5ExMono', 'HmIVP': 'F5IVP'}
K = [('-(2 * ', '-(5 * '), ('(2 * mlo c', '(5 * mlo c'), ('2 * qlo c', '5 * qlo c'), ('2 * qhi c', '5 * qhi c'),
     ('2 * P3', '5 * P3'), ('2 * y1', '5 * y1'), ('2 * P1', '5 * P1'), ('2 * evalQ c.pg', '5 * evalQ c.pg'),
     ('2 * evalQ c.pq', '5 * evalQ c.pq'), ('|2 * cl C', '|5 * cl C'), ('≤ 2 * C * 2', '≤ 5 * C * 2'),
     ('2 * T + 12', '5 * T + 24'), ('4 * T + 13', '10 * T + 25'),
     ('abs_two', 'abs_of_pos (by norm_num : (0 : ℝ) < 5)'),
     ('(qmul (qadd c.pg c.pg) c.pq)', '(qmul (qsmul 5 c.pg) c.pq)'),
     ('evalQ_qmul, ← dEvalQ_eq]', 'evalQ_qmul, evalQ_qsmul, ← dEvalQ_eq]'),
     ('1.3119376938', '1.5355261734'), ('1.3119376939', '1.5355261735'),
     ('−2 g q', '−5 g q'), ('−2 f q', '−5 f q'), ("2 g g''", "5 g g''"), ("2 f f''", "5 f f''"), ('2·pg·pq', '5·pg·pq'),
     ('(2 y1 − m)', '(5 y1 − m)'), ('(2 P3, s) and m = 2 mlo', '(5 P3, s) and m = 5 mlo'),
     ('(2 P3 ∈ {2 qlo, 2 qhi}', '(5 P3 ∈ {5 qlo, 5 qhi}'),
     ('os_homann', 'os_k5')]
def port(s, extra=()):
    for a, b in mods.items():
        s = re.sub(r'(Work|Checked)\.Homann\.' + a + r'\b', 'Work.FSFifth.' + b, s)
    s = s.replace('namespace Work.Homann', 'namespace Work.FSFifth').replace('end Work.Homann', 'end Work.FSFifth')
    s = s.replace('namespace Checked.Homann', 'namespace Work.FSFifth').replace('end Checked.Homann', 'end Work.FSFifth')
    s = s.replace('Work.Homann.homann_', 'Work.FSFifth.k5_').replace('Checked.Homann.homann_', 'Work.FSFifth.k5_')
    for a, b in K: s = s.replace(a, b)
    for a, b, n in extra:
        c = s.count(a); assert c == n, (a, c, n); s = s.replace(a, b)
    s = s.replace('Homann axisymmetric stagnation-point flow', 'Falkner–Skan β = 1/5 in scaled form (coefficient 5)')
    s = s.replace('the Homann field', 'the coefficient-5 field').replace('Homann', 'K = 5 (Falkner–Skan β = 1/5, scaled)')
    return s
H6 = [('Icc (0 : ℝ) 6', 'Icc (0 : ℝ) 4'), ('Icc 0 6', 'Icc 0 4')]
out = {}
for m in ['HmExBase', 'HmExFlow', 'HmExLimit', 'HmCellW', 'HmCellWC']:
    out[mods[m]] = port(open('Work/Homann/%s.lean' % m).read())
s = open('Work/Homann/HmExAssemble.lean').read()
out['F5ExAssemble'] = port(s, [(a, b, s.count(a)) for a, b in H6])
s = open('Checked/Homann/HmExMono.lean').read()
out['F5ExMono'] = port(s)
s = open('Checked/Homann/HmIVP.lean').read()
out['F5IVP'] = port(s)
for k, v in out.items():
    v = re.sub(r'^(import Mathlib\.[^\n]*\n)+', 'import Mathlib\n', v, flags=re.M) if not v.startswith('import Mathlib\n') else v
    open('Work/FSFifth/%s.lean' % k, 'w').write(v)
# emitters
for src, dst in [('emit_homann_w.py', 'emit_k5_w.py'), ('emit_homann_wc.py', 'emit_k5_wc.py')]:
    s = open('runs/2026-11-08T0428Z/scripts/' + src).read()
    s = s.replace('runs/2026-11-08T0428Z/scripts/gen_homann_w.py', 'runs/2026-11-08T2028Z/scripts/gen_k_w.py (FS_K = 5)')
    s = s.replace('runs/2026-11-08T0428Z/scripts/gen_homann_wc.py', 'runs/2026-11-08T2028Z/scripts/gen_k_wc.py (FS_K = 5)')
    s = s.replace('emit_homann_wc.py', 'emit_k5_wc.py').replace('emit_homann_w.py', 'emit_k5_w.py')
    s = port(s)
    open(R + dst, 'w').write(s)
print('ok')
