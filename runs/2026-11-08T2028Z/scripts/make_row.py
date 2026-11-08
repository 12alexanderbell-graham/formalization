#!/usr/bin/env python3
"""Run 2026-11-08T2028Z: one Falkner-Skan table row beta = 1/K (K an integer) from data to Work proofs, by the route
of the beta = 1/5 row (which this script reproduces up to module-doc wording).
usage: make_row.py K NS P LO HI H NAME FSLO FSHI SQLO SQHI MODE
  K       integer coefficient (beta = 1/K)          NS, P   Work namespace / module prefix (FSTenth, F10)
  LO, HI  certified window of F''(0) for F''' + K F F'' + 1 - F'^2 = 0 (cells from gen_k_w.py / gen_k_wc.py, FS_K = K)
  H       horizon of the cells                        NAME    file stem of the Falkner-Skan statements (TenthBounded)
  FSLO, FSHI  window of f''(0) in the Falkner-Skan statements; SQLO < sqrt K < SQHI rational bounds that transfer it
  MODE    'freeze' (Falkner-Skan statements with sorry) or 'prove' (port, emit, statements, proofs).
Data: runs/2026-11-08T2028Z/data/k<K>_{under,over,underC,overC}.json."""
import os, re, subprocess, sys
K, NS, P, LO, HI, H, NAME, FSLO, FSHI, SQLO, SQHI, MODE = sys.argv[1:13]
k = int(K); S = 'runs/2026-11-08T2028Z/scripts/'; D = 'runs/2026-11-08T2028Z/data/'
low = NAME[0].lower() + NAME[1:].replace('Bounded', '')   # e.g. tenth
FS = open('Work/FalknerSkan/FifthBounded.lean').read()
i = FS.index('\nnamespace'); j = FS.index('open Set Filter Topology', i)
def fs_stmts(proofs):
    s = FS
    s = s.replace('fs_fifth_', 'fs_%s_' % low).replace('Work.FalknerSkan.FifthBounded', 'Work.FalknerSkan.' + NAME)
    s = s.replace('1 / 5 * (1 - p', '1 / %d * (1 - p' % k).replace('1 / 5 * (1 - f1', '1 / %d * (1 - f1' % k)
    s = s.replace('(1 − f\'²)/5', '(1 − f\'²)/%d' % k).replace('(1 − p²)/5', '(1 − p²)/%d' % k)
    s = s.replace('0.6867081809', FSLO).replace('0.6867081811', FSHI).replace('β = 1/5', 'β = 1/%d' % k)
    s = s.replace('Work.FSFifth.F5Bounded', 'Work.%s.%sBounded' % (NS, P)).replace('k5_bounded', 'k%d_bounded' % k).replace('k5_exists', 'k%d_exists' % k)
    s = s.replace('Real.sqrt 5', 'Real.sqrt %d' % k).replace('sqrt5_lt', 'sqrt%d_lt' % k).replace('lt_sqrt5', 'lt_sqrt%d' % k)
    s = s.replace('2.2360679776', SQHI).replace('2.2360679774', SQLO).replace('c ^ 2 = 1 / 5', 'c ^ 2 = 1 / %d' % k)
    s = s.replace('(0 : ℝ) ≤ 5 by', '(0 : ℝ) ≤ %d by' % k).replace('(-(5 * (c * f', '(-(%d * (c * f' % k).replace('to_k5', 'to_k%d' % k)
    s = s.replace('-(5 * f η * q η) - 1 * (1 - p', '-(%d * f η * q η) - 1 * (1 - p' % k).replace('^ 2 = 5 := Real.sq_sqrt', '^ 2 = %d := Real.sq_sqrt' % k)
    s = s.replace('wedge half-angle π/10; tables print f\'\'(0) ≈ 0.686708', 'wedge exponent m = 1/%d' % (2 * k - 1))
    s = s.replace('F\'\'\' + 5 F F\'\'', 'F\'\'\' + %d F F\'\'' % k).replace('c = 1/√5', 'c = 1/√%d' % k).replace('by √5', 'by √%d' % k)
    s = s.replace('The coefficient-5 problem', 'The coefficient-%d problem' % k).replace('at 1.5355261734 and 1.5355261735', 'at %s and %s' % (LO, HI))
    s = s.replace('(`Work.FSFifth`', '(`Work.%s`' % NS).replace('run 2026-11-08T2028Z)', 'run 2026-11-08T2028Z, made by `runs/2026-11-08T2028Z/scripts/make_row.py`)', 1)
    if not proofs:
        s = re.sub(r'(?s)\nopen Set Filter Topology Checked.FalknerSkan.FSScale\n.*?\n(/-- Falkner–Skan)', r'\nopen Set Filter Topology\n\n\1', s, count=1)
        s = s.replace('import Mathlib\nimport Checked.FalknerSkan.FSScale\nimport Work.%s.%sBounded\n' % (NS, P), 'import Mathlib\n')
        s = re.sub(r'(?s)(:= by\n).*?(\n\n/--|\n\nend )', r'\1  sorry\2', s)
    assert '1 / 5' not in s and 'fifth' not in s.lower().replace('one-fifth', ''), [l for l in s.splitlines() if '1 / 5' in l or 'ifth' in l]
    return s
out = 'Work/FalknerSkan/%s.lean' % NAME
if MODE == 'freeze':
    t = fs_stmts(False); open(out, 'w').write(t); print('frozen', out); sys.exit(0)
# 1. port the Homann stack
subprocess.run(['python3', S + 'port_row.py', K, NS, P, LO, HI, H], check=True)
W = 'Work/%s/' % NS
for f in os.listdir(W):
    t = open(W + f).read()
    t = re.sub(r'`Work\.K = %d \(Falkner–Skan β = 1/%d, scaled\)\.H' % (k, k), '`Work.Hiemenz.H', t)
    t = t.replace('`homann_over`', '`k%d_over`' % k).replace('(run 2026-11-08T0428Z', '(run 2026-11-08T2028Z, make_row.py')
    if f == P + 'IVP.lean':
        t = re.sub(r'\(6 : ℝ\)', '(%s : ℝ)' % H, t); t = re.sub(r'\(6 : ℚ\)', '(%s : ℚ)' % H, t)
        t = re.sub(r'Icc \(0 : ℝ\) 6\b', 'Icc (0 : ℝ) ' + H, t); t = re.sub(r'Icc 0 6\b', 'Icc 0 ' + H, t); t = t.replace('[0, 6]', '[0, %s]' % H)
    open(W + f, 'w').write(t)
# 2. emit the data modules
for mode, json, mod, A in [('w', 'under', 'UData', LO), ('w', 'over', 'OData', HI), ('wc', 'underC', 'UDataC', LO), ('wc', 'overC', 'ODataC', HI)]:
    subprocess.run(['python3', S + 'emit_k%d_%s.py' % (k, mode), D + 'k%d_%s.json' % (k, json), '8', W + P + mod + '.lean', P + mod, A], check=True)
# 3. IVP chain bodies from the clamped data
def chain_text(mod, phi_old, spec_old):
    s = open(W + mod + '.lean').read()
    m = re.search(r"theorem chainC .*?\n(  have hX.*?\n)  rw \[hX\] at E (A\d+)\n", s, re.S)
    body, A = m.group(1), m.group(2)
    body = re.sub(r"obtain ⟨E, (P\d+)⟩ := ", r"obtain ⟨-, \1⟩ := ", body) + f"  rw [hX] at {A}\n  exact {A}\n"
    body = body.replace(f"(Φ := {phi_old})", "(Φ := BoxΦ)").replace(f"(fun c hok hsd => {spec_old} c hok hsd)", "(fun c hok _ => box_spec c hok)")
    return body
p = W + P + 'IVP.lean'; s = open(p).read()
bodies = list(re.finditer(r"  have hX.*?\n  exact A\d+\n", s, re.S)); assert len(bodies) == 2
s = s[:bodies[0].start()] + chain_text(P + 'UDataC', "(fun _ p _ t => p t < 1)", "sideU_spec") + s[bodies[0].end():bodies[1].start()] + chain_text(P + 'ODataC', "(fun _ _ q t => 0 < q t)", "sideO_spec") + s[bodies[1].end():]
open(p, 'w').write(s)
# 4. coefficient-K statements (from the beta = 1/5 row's FSFifth.lean) and the bounded-class module
def subst5(t):
    t = t.replace('Work.FSFifth.F5', 'Work.%s.%s' % (NS, P)).replace('Work.FSFifth', 'Work.' + NS).replace('k5_', 'k%d_' % k)
    t = t.replace('1.5355261734', LO).replace('1.5355261735', HI).replace('-(5 * ', '-(%d * ' % k).replace('(0:ℝ) ≤ 5)', '(0:ℝ) ≤ %d)' % k)
    t = t.replace('−5 f q', '−%d f q' % k).replace("5 f f''", "%d f f''" % k).replace("5 F F''", "%d F F''" % k).replace('β = 1/5', 'β = 1/%d' % k)
    t = t.replace('coefficient 5', 'coefficient %d' % k).replace('coefficient is\n5', 'coefficient is\n%d' % k).replace('Coefficient 5', 'Coefficient %d' % k).replace('coefficient-5', 'coefficient-%d' % k)
    t = t.replace('FS_K = 5', 'FS_K = %d' % k).replace('Work.FalknerSkan.FifthBounded', 'Work.FalknerSkan.' + NAME)
    t = t.replace('f(s√5)/√5', 'f(s√%d)/√%d' % (k, k)).replace('(S ≥ 4)', '(S ≥ %s)' % H).replace('(0, 4]', '(0, %s]' % H)
    return t
s = open('Work/FSFifth/FSFifth.lean').read()
for a, b, n in [('4 ≤ S', H + ' ≤ S', 2), ('Ioc (0 : ℝ) 4', 'Ioc (0 : ℝ) ' + H, 2), ('Icc (0 : ℝ) 4', 'Icc (0 : ℝ) ' + H, 2), ('⟨4, ⟨by norm_num', '⟨%s, ⟨by norm_num' % H, 2), ('S ≥ 4', 'S ≥ ' + H, None), ('(0, 4]', '(0, %s]' % H, None)]:
    if n is not None: assert s.count(a) == n, (a, s.count(a))
    s = s.replace(a, b)
open(W + NS + '.lean', 'w').write(subst5(s))
s = open('Work/FSFifth/F5Bounded.lean').read()
s = s.replace('Work.FSFifth.k5_under 4', 'Work.FSFifth.k5_under ' + H).replace('Work.FSFifth.k5_over 4', 'Work.FSFifth.k5_over ' + H).replace('Icc (0 : ℝ) 4', 'Icc (0 : ℝ) ' + H)
open(W + P + 'Bounded.lean', 'w').write(subst5(s))
# 5. Falkner-Skan statements with proofs
t = fs_stmts(True); open(out, 'w').write(t)
for f in os.listdir(W):
    t = open(W + f).read()
    assert 'FSFifth' not in t and '1.5355261' not in t, f
print('row made', NS, NAME)
