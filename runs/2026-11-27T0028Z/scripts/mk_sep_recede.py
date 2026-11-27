#!/usr/bin/env python3
"""Run 2026-11-27T0028Z: write Checked/FSSep/RecedeSep.lean, the separation stack at the start (0, -1/1000, 0)
(a wall receding against the stream), by asserted replacements on Checked/FSSep/BlowSep.lean (the stack at
(cS, 0, 0) with the energy corrected for f >= cS = -1/1000 and K <= 6 down the stack).

What changes (plan: runs/2026-11-26T1828Z/README.md, section Part 1):
  * p >= -1/1000 instead of p >= 0 (p is non-decreasing while q >= 0);
  * new lemmas `early` and `late`: while p < 0 on [0, 1/21], f lies in [-s/1000, 0], so q' >= 1 - p^2 >= 99/100,
    q >= 99 s/100 and p(1/21) >= -1/1000 + 99/(200*441) > 0; hence p >= 0 from s = 1/20 on;
  * f >= cS from f + s/1000 non-decreasing (s <= 1/20) and f non-decreasing on [1/20, t];
  * the unclamping conclusions carry (-1/1000 <= p t /\\ (1/20 <= t -> 0 <= p t)) in place of 0 <= p t;
  * the slow-event and limit steps take p >= 0 from `late`."""
import pathlib
R = pathlib.Path(__file__).resolve().parents[3]
s = (R / 'Checked/FSSep/BlowSep.lean').read_text()
def rep(a, b, n=1):
    global s
    assert s.count(a) == n, (a[:90], s.count(a), n); s = s.replace(a, b)

P0 = '-(1 / 1000)'
# ---- names, start
rep('namespace Checked.FSSep.BlowSep', 'namespace Checked.FSSep.RecedeSep')
rep('end Checked.FSSep.BlowSep', 'end Checked.FSSep.RecedeSep')
rep('/-- The blowing value of the start, minus one thousandth. -/', '/-- The lower bound of the stream function along the receding-wall trajectories, minus one thousandth. -/')
rep('''/-- The certified chain shape from (cS, 0, 0): every solution of the clamped coefficient-K field on [0, T] from
(cS, 0, 0) has the event `E`. -/
def ChainKS''', f'''/-- The certified chain shape from (0, {P0}, 0): every solution of the clamped coefficient-K field on [0, T] from
that start has the event `E`. -/
def ChainKR''')
rep('Y 0 = (cS, 0, 0)', f'Y 0 = (0, {P0}, 0)', 4)
rep('      (cS, (0 : ℝ), (0 : ℝ)) (Real.toNNReal (L * T))', f'      ((0 : ℝ), ({P0} : ℝ), (0 : ℝ)) (Real.toNNReal (L * T))')
rep('/-- The flow of the clamped coefficient-K field from (cS, 0, 0). -/', '/-- The flow of the clamped coefficient-K field from (0, wall velocity, 0). -/')
rep('theorem flowK_zero (K : ℝ) : flowK K 0 = (cS, 0, 0)', f'theorem flowK_zero (K : ℝ) : flowK K 0 = (0, {P0}, 0)')
rep('(h : ChainKS K E) : E (flowK K)', '(h : ChainKR K E) : E (flowK K)')
rep('(hf0 : f 0 = cS) (hp0 : p 0 = 0) (hq0 : q 0 = 0)', f'(hf0 : f 0 = 0) (hp0 : p 0 = {P0}) (hq0 : q 0 = 0)', 3)
rep('''  have hv : -(K * cl (max (0 : ℝ) 0 + 2) (f 0) * cl 2 (q 0)) + 1 - cl 2 (p 0) ^ 2 = 1 := by
    rw [hf0, hp0, hq0]; norm_num [cl]
  rw [hv] at h
  exact Checked.FSSep.SUnclamp.q_pos_start h one_pos hq0''', '''  have hv : -(K * cl (max (0 : ℝ) 0 + 2) (f 0) * cl 2 (q 0)) + 1 - cl 2 (p 0) ^ 2 = 999999 / 1000000 := by
    rw [hf0, hp0, hq0]; norm_num [cl]
  rw [hv] at h
  exact Checked.FSSep.SUnclamp.q_pos_start h (by norm_num) hq0''')

# ---- early / late, inserted before unclampS
EL = f'''
/-- Near a receding wall the velocity turns positive before s = 1/21: while p < 0 on [0, 1/21] the stream function
lies in [-s/1000, 0], so the shear grows at rate at least 99/100 and p(1/21) ≥ -1/1000 + 99/(200·441) > 0. -/
theorem early {{K : ℝ}} (hK : 0 < K) {{f p q : ℝ → ℝ}}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (cl 2 (p η)) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (cl 2 (q η)) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q
      (-(K * cl (max η 0 + 2) (f η) * cl 2 (q η)) + 1 - cl 2 (p η) ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = {P0}) (hq0 : q 0 = 0)
    (hpm : MonotoneOn p (Icc 0 (1 / 21)))
    (hb : ∀ s ∈ Icc (0 : ℝ) (1 / 21), 0 ≤ q s ∧ q s ≤ 2) :
    0 ≤ p (1 / 21) := by
  have h00 : (0 : ℝ) ≤ 0 := le_rfl
  have hσ : (0 : ℝ) ≤ 1 / 21 := by norm_num
  have hσI : (1 / 21 : ℝ) ∈ Icc (0 : ℝ) (1 / 21) := ⟨hσ, le_rfl⟩
  by_contra hneg
  push Not at hneg
  have hpI : ∀ s ∈ Icc (0 : ℝ) (1 / 21), {P0} ≤ p s ∧ p s < 0 := fun s hs => by
    refine ⟨?_, lt_of_le_of_lt (hpm hs hσI hs.2) hneg⟩
    have := hpm ⟨le_rfl, hσ⟩ hs hs.1
    rw [hp0] at this; exact this
  have ceq := @Checked.FSSep.SUnclamp.cl_eq
  have hfa : AntitoneOn f (Icc 0 (1 / 21)) := anti hf h00 (fun x hx => by
    have := hpI x ⟨hx.1.le, hx.2.le⟩
    rw [ceq (by linarith) (by linarith)]; exact this.2.le)
  have hfle : ∀ s ∈ Icc (0 : ℝ) (1 / 21), f s ≤ 0 := fun s hs => by
    have := hfa ⟨le_rfl, hσ⟩ hs hs.1; rwa [hf0] at this
  have hfd : MonotoneOn (fun s => f s + 1 / 1000 * s) (Icc 0 (1 / 21)) :=
    mono (g' := fun s => cl 2 (p s) + 1 / 1000 * 1)
      (fun η hη => (hf η hη).add ((hasDerivWithinAt_id η (Ici 0)).const_mul (1 / 1000))) h00
      (fun x hx => by
        have := hpI x ⟨hx.1.le, hx.2.le⟩
        rw [ceq (by linarith) (by linarith)]; linarith [this.1])
  have hfge : ∀ s ∈ Icc (0 : ℝ) (1 / 21), -(1 / 1000) * s ≤ f s := fun s hs => by
    have := hfd ⟨le_rfl, hσ⟩ hs hs.1
    dsimp only at this; rw [hf0] at this; linarith
  have hqm : MonotoneOn (fun s => q s - 99 / 100 * s) (Icc 0 (1 / 21)) :=
    mono (g' := fun s => (-(K * cl (max s 0 + 2) (f s) * cl 2 (q s)) + 1 - cl 2 (p s) ^ 2) - 99 / 100 * 1)
      (fun η hη => (hq η hη).sub ((hasDerivWithinAt_id η (Ici 0)).const_mul (99 / 100))) h00
      (fun x hx => by
        have hx' : x ∈ Icc (0 : ℝ) (1 / 21) := ⟨hx.1.le, hx.2.le⟩
        obtain ⟨a1, a2⟩ := hpI x hx'
        obtain ⟨b1, b2⟩ := hb x hx'
        have c1 := hfle x hx'
        have c2 := hfge x hx'
        rw [ceq (c := max x 0 + 2) (y := f x) (by rw [max_eq_left hx'.1]; linarith)
            (by rw [max_eq_left hx'.1]; linarith),
          ceq (c := 2) (y := q x) (by linarith) b2, ceq (c := 2) (y := p x) (by linarith) (by linarith)]
        have e : 0 ≤ K * (-f x) * q x := mul_nonneg (mul_nonneg hK.le (by linarith)) b1
        have hp2 : p x ^ 2 ≤ 1 / 1000000 := by nlinarith
        nlinarith)
  have hqge : ∀ s ∈ Icc (0 : ℝ) (1 / 21), 99 / 100 * s ≤ q s := fun s hs => by
    have := hqm ⟨le_rfl, hσ⟩ hs hs.1
    dsimp only at this; rw [hq0] at this; linarith
  have hpm2 : MonotoneOn (fun s => p s - 99 / 200 * (s * s)) (Icc 0 (1 / 21)) :=
    mono (g' := fun s => cl 2 (q s) - 99 / 200 * (1 * s + s * 1))
      (fun η hη => (hp η hη).sub
        (((hasDerivWithinAt_id η (Ici 0)).mul (hasDerivWithinAt_id η (Ici 0))).const_mul (99 / 200))) h00
      (fun x hx => by
        have hx' : x ∈ Icc (0 : ℝ) (1 / 21) := ⟨hx.1.le, hx.2.le⟩
        obtain ⟨b1, b2⟩ := hb x hx'
        rw [ceq (by linarith) b2]
        have := hqge x hx'
        linarith)
  have := hpm2 ⟨le_rfl, hσ⟩ hσI hσ
  dsimp only at this
  rw [hp0] at this
  norm_num at this
  linarith

/-- Along a receding-wall trajectory with 0 ≤ q < 2 before τ and p non-decreasing on [0, τ], p ≥ 0 from s = 1/20
on (`early`). -/
theorem late {{K : ℝ}} (hK : 0 < K) {{f p q : ℝ → ℝ}}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (cl 2 (p η)) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (cl 2 (q η)) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q
      (-(K * cl (max η 0 + 2) (f η) * cl 2 (q η)) + 1 - cl 2 (p η) ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = {P0}) (hq0 : q 0 = 0) {{τ : ℝ}}
    (good : ∀ s ∈ Ico 0 τ, 0 ≤ q s ∧ q s < 2) (hpm : MonotoneOn p (Icc 0 τ)) :
    ∀ s ∈ Icc 0 τ, 1 / 20 ≤ s → 0 ≤ p s := by
  intro s hs h20
  have h21 : (1 / 21 : ℝ) < τ := by linarith [hs.2]
  have e := early hK hf hp hq hf0 hp0 hq0 (hpm.mono (Icc_subset_Icc le_rfl h21.le))
    (fun x hx => ⟨(good x ⟨hx.1, lt_of_le_of_lt hx.2 h21⟩).1, (good x ⟨hx.1, lt_of_le_of_lt hx.2 h21⟩).2.le⟩)
  exact e.trans (hpm ⟨by norm_num, h21.le⟩ hs (by linarith))

set_option maxHeartbeats 1000000 in
theorem unclampS'''
rep('\nset_option maxHeartbeats 1000000 in\ntheorem unclampS', EL)

# ---- conclusions
rep('''    ∀ t ∈ Ici (0 : ℝ), 0 ≤ p t ∧ p t < 1 ∧ 0 ≤ q t ∧ (0 < t → 0 < q t) ∧ q t < 2 ∧ cS ≤ f t ∧ f t ≤ t ∧
      (η₀ ≤ t → q t < 3 * (1 - p t) ∧ 11 / 15 < f t) := by''',
f'''    ∀ t ∈ Ici (0 : ℝ), ({P0} ≤ p t ∧ (1 / 20 ≤ t → 0 ≤ p t)) ∧ p t < 1 ∧ 0 ≤ q t ∧ (0 < t → 0 < q t) ∧ q t < 2 ∧
      cS ≤ f t ∧ f t ≤ t ∧ (η₀ ≤ t → q t < 3 * (1 - p t) ∧ 11 / 15 < f t) := by''')
rep('''    ∀ t ∈ Ici (0 : ℝ), 0 ≤ p t ∧ p t ≤ 1 ∧ 0 ≤ q t ∧ (0 < t → 0 < q t) ∧ q t < 2 ∧ cS ≤ f t ∧ f t ≤ t := by''',
f'''    ∀ t ∈ Ici (0 : ℝ), ({P0} ≤ p t ∧ (1 / 20 ≤ t → 0 ≤ p t)) ∧ p t ≤ 1 ∧ 0 ≤ q t ∧ (0 < t → 0 < q t) ∧ q t < 2 ∧
      cS ≤ f t ∧ f t ≤ t := by''')
rep('(∀ s ∈ Icc 0 τ, 0 ≤ p s ∧ p s ≤ 1 ∧ 0 ≤ q s ∧ q s ≤ 2 ∧ cS ≤ f s ∧ f s ≤ s) := by',
    f'(∀ s ∈ Icc 0 τ, {P0} ≤ p s ∧ p s ≤ 1 ∧ 0 ≤ q s ∧ q s ≤ 2 ∧ cS ≤ f s ∧ f s ≤ s) := by', 2)
rep('''    have hpge : ∀ s ∈ Icc 0 τ, 0 ≤ p s := fun s hs => by
      have := hpm ⟨le_rfl, hτ⟩ hs hs.1; rwa [hp0] at this''', f'''    have hpge : ∀ s ∈ Icc 0 τ, {P0} ≤ p s := fun s hs => by
      have := hpm ⟨le_rfl, hτ⟩ hs hs.1; rwa [hp0] at this''', 2)
# f: f + s/1000 non-decreasing, f non-decreasing from 1/20 on
FD = lambda goodq: f'''    have hpl := late hK0 hf hp hq hf0 hp0 hq0 (fun s hs => {goodq}) hpm
    have hfd : MonotoneOn (fun s => f s + 1 / 1000 * s) (Icc 0 τ) :=
      mono (g' := fun s => cl 2 (p s) + 1 / 1000 * 1)
        (fun η hη => (hf η hη).add ((hasDerivWithinAt_id η (Ici 0)).const_mul (1 / 1000))) h00
        (fun x hx => by
          have := hpge x ⟨hx.1.le, hx.2.le⟩
          have h1 := HP1
          rw [Checked.FSSep.SUnclamp.cl_eq (by linarith) (by linarith)]; linarith)
    have hfm : MonotoneOn f (Icc (1 / 20) τ) := mono hf (by norm_num) (fun x hx => by
      have := hpl x ⟨by linarith [hx.1], hx.2.le⟩ hx.1.le
      have h1 := HP1
      rw [Checked.FSSep.SUnclamp.cl_eq (by linarith) (by linarith)]; exact this)'''
old_fm1 = '''    have hfm : MonotoneOn f (Icc 0 τ) := mono hf h00 (fun x hx => by
      have g := good x ⟨hx.1.le, hx.2⟩
      have := hpge x ⟨hx.1.le, hx.2.le⟩
      rw [Checked.FSSep.SUnclamp.cl_eq (by linarith) (by linarith)]; exact this)'''
rep(old_fm1, FD('⟨(good s hs).2.1, (good s hs).2.2⟩').replace('HP1', '(good x ⟨by linarith [hx.1], hx.2⟩).1'))
old_fm2 = '''    have hfm : MonotoneOn f (Icc 0 τ) := mono hf h00 (fun x hx => by
      have := hpge x ⟨hx.1.le, hx.2.le⟩
      have h1 := hp1 x hx.1.le
      rw [Checked.FSSep.SUnclamp.cl_eq (by linarith) (by linarith)]; exact this)'''
rep(old_fm2, FD('good s hs').replace('HP1', 'hp1 x (show (0 : ℝ) ≤ x by linarith [hx.1])').replace('late hK0', 'late hK'))
HFS = '''    have hfs : cS ≤ f s := by
      have hcSe : cS = -(1 / 1000) := rfl
      rcases le_total s (1 / 20) with h | h
      · have := hfd ⟨le_rfl, hτ⟩ hs hs.1
        dsimp only at this; rw [hf0] at this; linarith
      · have h1 := hfd ⟨le_rfl, hτ⟩ ⟨by norm_num, h.trans hs.2⟩ (by norm_num)
        have h2 := hfm ⟨le_rfl, h.trans hs.2⟩ ⟨h, hs.2⟩ h
        dsimp only at h1; rw [hf0] at h1; linarith'''
rep('    have hfs : cS ≤ f s := by have := hfm ⟨le_rfl, hτ⟩ hs hs.1; rw [hf0] at this; linarith', HFS, 2)
rep('      · subst h0; rw [hp0, hq0]; exact ⟨le_rfl, by norm_num, le_rfl, by norm_num, hfs, hfs2⟩',
    '      · subst h0; rw [hp0, hq0]; exact ⟨by norm_num, by norm_num, le_rfl, by norm_num, hfs, hfs2⟩')
rep('      · subst h0; rw [hq0]; exact ⟨hps, hp1s, le_rfl, by norm_num, hfs, hfs2⟩',
    '      · subst h0; rw [hq0]; exact ⟨hps, hp1s, le_rfl, by norm_num, hfs, hfs2⟩')
# energy: p - p^3/3 <= 2/3 for p >= -2
rep('      have hp3 : p τ - p τ ^ 3 / 3 ≤ 2 / 3 := by nlinarith [sq_nonneg (p τ - 1)]',
    '      have hp3 : p τ - p τ ^ 3 / 3 ≤ 2 / 3 := by\n        nlinarith [mul_nonneg (sq_nonneg (p τ - 1)) (show (0 : ℝ) ≤ p τ + 2 by linarith)]', 2)
# the late slow event: f non-decreasing on [η₀, τ] (p ≥ 0 there, η₀ > 11/15)
rep('''      have hfm : MonotoneOn f (Icc 0 τ) := mono hf h00 (fun x hx => by
        have hx' : x ∈ Icc 0 τ := ⟨hx.1.le, hx.2.le⟩
        rw [tf x hx']; exact (C x hx').1)
      have hfτ : 11 / 15 < f τ := lt_of_lt_of_le hs3 (hfm ⟨hη₀.le, hle⟩ hτI hle)''',
'''      have hpmτ : MonotoneOn p (Icc 0 τ) := mono hp h00 (fun x hx => by
        have hx' : x ∈ Icc 0 τ := ⟨hx.1.le, hx.2.le⟩
        rw [tp x hx']; exact (C x hx').2.2.1)
      have hpl := late hK0 hf hp hq hf0 hp0 hq0 (fun s hs => ⟨qnn s hs, (good s hs).2.2.1⟩) hpmτ
      have hη20 : 1 / 20 ≤ η₀ := by have := (C η₀ ⟨hη₀.le, hle⟩).2.2.2.2.2; linarith
      have hfm : MonotoneOn f (Icc η₀ τ) := mono hf hη₀.le (fun x hx => by
        have hx' : x ∈ Icc 0 τ := ⟨hη₀.le.trans hx.1.le, hx.2.le⟩
        rw [tf x hx']; exact hpl x hx' (by linarith [hx.1]))
      have hfτ : 11 / 15 < f τ := lt_of_lt_of_le hs3 (hfm ⟨le_rfl, hle⟩ ⟨hle, le_rfl⟩ hle)''')
# final assemblies
rep('''  have C := conseq t ht0 (fun s hs => by
    have := M s ⟨hs.1, hs.2.le⟩
    refine ⟨this.1, ?_, this.2.2.1⟩
    rcases eq_or_lt_of_le hs.1 with h | h
    · rw [← h, hq0]
    · exact (this.2.1 h).le) t ⟨ht0, le_rfl⟩
  have Mt := M t ⟨ht0, le_rfl⟩
  exact ⟨C.1, Mt.1, C.2.2.1, Mt.2.1, Mt.2.2.1, C.2.2.2.2.1, C.2.2.2.2.2, Mt.2.2.2⟩''',
'''  have qg : ∀ s ∈ Ico 0 t, 0 ≤ q s ∧ q s < 2 := fun s hs => by
    have := M s ⟨hs.1, hs.2.le⟩
    refine ⟨?_, this.2.2.1⟩
    rcases eq_or_lt_of_le hs.1 with h | h
    · rw [← h, hq0]
    · exact (this.2.1 h).le
  have Call := conseq t ht0 (fun s hs => ⟨(M s ⟨hs.1, hs.2.le⟩).1, qg s hs⟩)
  have C := Call t ⟨ht0, le_rfl⟩
  have hpmt : MonotoneOn p (Icc 0 t) := mono hp h00 (fun x hx => by
    have c := Call x ⟨hx.1.le, hx.2.le⟩
    rw [Checked.FSSep.SUnclamp.cl_eq (by linarith [c.2.2.1]) c.2.2.2.1]; exact c.2.2.1)
  have Mt := M t ⟨ht0, le_rfl⟩
  exact ⟨⟨C.1, late hK0 hf hp hq hf0 hp0 hq0 qg hpmt t ⟨ht0, le_rfl⟩⟩, Mt.1, C.2.2.1, Mt.2.1, Mt.2.2.1,
    C.2.2.2.2.1, C.2.2.2.2.2, Mt.2.2.2⟩''')
rep('''  have C := conseq t ht0 (fun s hs => by
    have := M s ⟨hs.1, hs.2.le⟩
    refine ⟨?_, this.2⟩
    rcases eq_or_lt_of_le hs.1 with h | h
    · rw [← h, hq0]
    · exact (this.1 h).le) t ⟨ht0, le_rfl⟩
  have Mt := M t ⟨ht0, le_rfl⟩
  exact ⟨C.1, C.2.1, C.2.2.1, Mt.1, Mt.2, C.2.2.2.2.1, C.2.2.2.2.2⟩''',
'''  have qg : ∀ s ∈ Ico 0 t, 0 ≤ q s ∧ q s < 2 := fun s hs => by
    have := M s ⟨hs.1, hs.2.le⟩
    refine ⟨?_, this.2⟩
    rcases eq_or_lt_of_le hs.1 with h | h
    · rw [← h, hq0]
    · exact (this.1 h).le
  have Call := conseq t ht0 qg
  have C := Call t ⟨ht0, le_rfl⟩
  have hpmt : MonotoneOn p (Icc 0 t) := mono hp h00 (fun x hx => by
    have c := Call x ⟨hx.1.le, hx.2.le⟩
    rw [Checked.FSSep.SUnclamp.cl_eq (by linarith [c.2.2.1]) c.2.2.2.1]; exact c.2.2.1)
  have Mt := M t ⟨ht0, le_rfl⟩
  exact ⟨⟨C.1, late hK hf hp hq hf0 hp0 hq0 qg hpmt t ⟨ht0, le_rfl⟩⟩, C.2.1, C.2.2.1, Mt.1, Mt.2,
    C.2.2.2.2.1, C.2.2.2.2.2⟩''')
# ---- downstream
rep('''    ∀ t ∈ Ici (0 : ℝ), 0 ≤ (flowK K t).2.1 ∧ (flowK K t).2.1 < 1 ∧ 0 ≤ (flowK K t).2.2 ∧''',
    f'''    ∀ t ∈ Ici (0 : ℝ), ({P0} ≤ (flowK K t).2.1 ∧ (1 / 20 ≤ t → 0 ≤ (flowK K t).2.1)) ∧ (flowK K t).2.1 < 1 ∧
      0 ≤ (flowK K t).2.2 ∧''')
rep('''  have hpη : 0 < (flowK K₀ η).2.1 := by
    obtain ⟨_, hP, _⟩ := comps K₀
    have hsm := Checked.FalknerSkan.LimitCore.smono hP le_rfl (b := η) (fun x hx => by
      have u := U x hx.1.le
      rw [Checked.FSSep.SUnclamp.cl_eq (by linarith [u.2.2.1]) (by linarith [u.2.2.2.2.1])]
      exact u.2.2.2.1 hx.1)
    have := hsm ⟨le_rfl, hη.le⟩ ⟨hη.le, le_rfl⟩ hη
    simpa [flowK_zero] using this''',
'''  have hpη : 0 < (flowK K₀ η).2.1 := by
    obtain ⟨_, hP, _⟩ := comps K₀
    have hη20 : 1 / 20 < η := by have u := U η hη.le; linarith [u.2.2.2.2.2.2.1]
    have hsm := Checked.FalknerSkan.LimitCore.smono hP (by norm_num : (0 : ℝ) ≤ 1 / 20) (b := η) (fun x hx => by
      have u := U x (show (0 : ℝ) ≤ x by linarith [hx.1])
      rw [Checked.FSSep.SUnclamp.cl_eq (by linarith [u.2.2.1]) (by linarith [u.2.2.2.2.1])]
      exact u.2.2.2.1 (by linarith [hx.1]))
    have := hsm ⟨le_rfl, hη20.le⟩ ⟨hη20.le, le_rfl⟩ hη20
    linarith [(U (1 / 20) (by norm_num)).1.2 le_rfl]''')
rep('''  have hF0 : F 0 = cS := by simp [F, h0]
  have hP0 : P 0 = 0 := by simp [P, h0]''', f'''  have hF0 : F 0 = 0 := by simp [F, h0]
  have hP0 : P 0 = {P0} := by simp [P, h0]''')
rep('    have := hF η hη; rwa [ceq (by linarith [u.1]) (by linarith [u.2.1])] at this',
    '    have := hF η hη; rwa [ceq (by linarith [u.1.1]) (by linarith [u.2.1])] at this')
rep('      ceq (c := 2) (y := P η) (by linarith [u.1]) (by linarith [u.2.1])] at this',
    '      ceq (c := 2) (y := P η) (by linarith [u.1.1]) (by linarith [u.2.1])] at this')
rep('      (by linarith [(U 1 (by norm_num)).1])', '      (by linarith [(U 1 (by norm_num)).1.2 (by norm_num)])')
rep('''      (U η (ha0.trans hη')).1, hc, hN η ((le_max_left N 1).trans hη')⟩''',
    '''      (U η (ha0.trans hη')).1.2 (by linarith [(le_max_right N 1).trans hη']), hc, hN η ((le_max_left N 1).trans hη')⟩''')
rep('theorem core_sepS {lo hi : ℝ} (hlo5 : 5 ≤ lo) (hlh : lo < hi) (hhi6 : hi ≤ 6) (hO : ChainKS lo Over) (hS : ChainKS hi SlowS) :',
    'theorem core_sepR {lo hi : ℝ} (hlo5 : 5 ≤ lo) (hlh : lo < hi) (hhi6 : hi ≤ 6) (hO : ChainKR lo Over) (hS : ChainKR hi SlowS) :')
rep('      f 0 < 0 ∧ p 0 = 0 ∧ q 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧', '      f 0 = 0 ∧ p 0 < 0 ∧ q 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧')
rep('''  have hF0 : F 0 = cS := by simp [F, flowK_zero]
  have hP0 : P 0 = 0 := by simp [P, flowK_zero]''', f'''  have hF0 : F 0 = 0 := by simp [F, flowK_zero]
  have hP0 : P 0 = {P0} := by simp [P, flowK_zero]''')
rep('''    by simp only [zero_div, hF0]; exact mul_neg_of_pos_of_neg hc cS_neg,
    by simp [hP0], by simp [hQ0],''', '''    by simp [hF0], by simp only [zero_div, hP0]; norm_num, by simp [hQ0],''')
# module doc
import re
doc = ('/-! Falkner–Skan separation with the wall receding against the stream: the separation stack (`SFlow`, '
       '`SUnclamp`, `SAssemble`, as ported in `BlowSep`) at the start (0, w, 0) of the clamped adverse-sign field, w minus '
       'one thousandth. The velocity is negative only near the wall and non-negative from one twentieth on (`early`, '
       '`late`), so the stream function stays above minus one thousandth and the corrected energy of `BlowSep` applies; '
       'the shooting core takes the two certified chain coefficients as parameters. Written by '
       '`runs/2026-11-27T0028Z/scripts/mk_sep_recede.py`. Module `RecedeSep`. -/')
s = re.sub(r'/-!.*?-/', lambda m: doc, s, count=1, flags=re.S)
(R / 'Checked/FSSep/RecedeSep.lean').write_text(s)
print('wrote Checked/FSSep/RecedeSep.lean', s.count('\n'), 'lines')
