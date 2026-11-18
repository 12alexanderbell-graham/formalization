"""Emit the remaining witness theorems (run 2026-11-18T0628Z)."""
P = {1: ('S1', '1 / 2', 'log_s2', 'd1_bd'), 3: ('S3', '3 / 2', 'log_2s2', 'd3_bd'),
     5: ('S5', '5 / 2', 'log_4s2', 'd5_bd')}
coef = {'fit17': ('(47 / 4 : ℝ)', '(9 / 2 : ℝ)', '2.1832'), 'fit18': ('(171 / 4 : ℝ)', '(-23:ℝ)', '3.5495'),
        'fit19': ('(8:ℝ)', '(-21 / 4 : ℝ)', '1.0706'), 'fit9': ('(1 / 2 : ℝ)', '(7 / 2 : ℝ)', '0.5895'),
        'rl11': ('(69 / 20 : ℝ)', '(83 / 50 : ℝ)', '0.7993')}
def pos(w, i):
    S, k, lg, _ = P[i]
    return f'''  · rw [{S}.1, poly3_eq _ _ _ ({k}) _ {lg}]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_{w}_{i}.1 (by norm_num) (by norm_num)'''
def hm(w, i):
    S, k, lg, d = P[i]
    return f'''  · rw [{S}.2, {S}.1, poly3_eq _ _ _ ({k}) _ {lg}]
    exact band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_{w}_{i}.1 B_{w}_{i}.2 {d}.1 {d}.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)'''
head = '''  obtain ⟨o53, o31, o10, p5, p3⟩ := ord
  obtain ⟨l1, l2⟩ := log10_bd
  obtain ⟨m1, m2⟩ := lam_bd
  obtain ⟨n1, n2⟩ := log2L_bd'''
def thm(name, hl, doc, w, srcs, tstart, times, omega, extra, hms, concl, law=True):
    """srcs: sources (1,3,5 indices) for t5,t3,t1 positions."""
    a2, a3, H = coef[w]
    hyp = f'  obtain ⟨hp, hd, hH₀, hH⟩ := ea_hyps _ {tstart}'
    body = [f'/-- {doc} -/', f'theorem {name} : necessity% {hl} := by', head, hyp,
            f'  refine ⟨{omega}, {times}, hp, hd, hH₀, {"hH, " if law else ""}{extra}',
            f'    {a2}, {a3}, {H}, 0, ' + ', '.join(['by norm_num'] + ['?_'] * (3 + len(hms) + 1)) + '⟩']
    for i in srcs: body.append(pos(w, i))
    for i in hms: body.append(hm(w, i))
    body.append(concl)
    return '\n'.join(body) + '\n'
FD = 'Checked.Cosmography.B1Fit.fit_direction'
RL = 'Checked.Cosmography.B1FitRL19.rl19_box_unmatched'
cn = '  · apply concl_neg; norm_num; nlinarith'
out = []
out.append(thm('fit_direction_h18', FD + ' 18',
  'Without the residual condition at `1 + z = 2√2`: the cubic `a₂ = 171/4`, `a₃ = −23` matches at `√2` and `4√2`.',
  'fit18', (1, 3, 5), 'p5', 'by norm_num, le_rfl, ea, _, _, _, 1, o53, o31, o10', '1',
  'S1.1, S3.1, S5.1,', (1, 5), cn).replace('refine ⟨1, by norm_num, le_rfl, ea', 'refine ⟨1, by norm_num, le_rfl, ea'))
out.append(thm('fit_direction_h19', FD + ' 19',
  'Without the residual condition at `1 + z = 4√2`: the cubic `a₂ = 8`, `a₃ = −21/4` matches at `√2` and `2√2`.',
  'fit19', (1, 3, 5), 'p5', 'by norm_num, le_rfl, ea, _, _, _, 1, o53, o31, o10', '1',
  'S1.1, S3.1, S5.1,', (1, 3), cn))
out.append(thm('fit_direction_h9', FD + ' 9',
  'Without the expansion law: the Einstein–de Sitter scale factor with the law\'s density read as zero; the cubic `a₂ = 1/2`, `a₃ = 7/2` matches all three distance moduli and lies on the wrong side of the line through the density-zero point.',
  'fit9', (1, 3, 5), 'p5', 'by norm_num, by norm_num, ea, _, _, _, 1, o53, o31, o10', '0',
  'S1.1, S3.1, S5.1,', (1, 3, 5), cn, law=False))
# coincident source times
out.append(thm('fit_direction_h10', FD + ' 10',
  'Without the redshift of the nearest source: that source placed at the middle one (`1 + z = 2√2`); the cubic of `fit_direction_h17` matches both distinct sources.',
  'fit17', (3, 3, 5), 'p5', 'by norm_num, le_rfl, ea, _, tE (2 * √2), tE (2 * √2), 1, o53, le_rfl, le_trans o31 o10', '1',
  'S3.1, S5.1,', (3, 3, 5), cn))
out.append(thm('fit_direction_h11', FD + ' 11',
  'Without the redshift of the middle source: that source placed at the nearest one (`1 + z = √2`); the cubic of `fit_direction_h18` matches both distinct sources.',
  'fit18', (1, 1, 5), 'p5', 'by norm_num, le_rfl, ea, _, tE √2, tE √2, 1, le_trans o53 o31, le_rfl, o10', '1',
  'S1.1, S5.1,', (1, 1, 5), cn))
out.append(thm('fit_direction_h12', FD + ' 12',
  'Without the redshift of the farthest source: that source placed at the middle one (`1 + z = 2√2`); the cubic of `fit_direction_h19` matches both distinct sources.',
  'fit19', (1, 3, 3), 'p3', 'by norm_num, le_rfl, ea, tE (2 * √2), tE (2 * √2), _, 1, le_rfl, o31, o10', '1',
  'S1.1, S3.1,', (1, 3, 3), cn))
print('\n'.join(out))
