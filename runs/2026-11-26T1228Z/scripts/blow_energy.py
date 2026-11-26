#!/usr/bin/env python3
"""Run 2026-11-26T1228Z (SCRATCH): post-process runs/2026-11-26T1228Z/lean/BlowSep.lean (from mk_sep_blow_scratch.py):
the energy step with f >= cS = -1/1000 instead of f >= 0. Since 0 <= q <= 2 on the good interval,
-K f q^2 <= (K/1000) q^2 <= (2K/1000) q = (2K/1000) p', so H - (2K/1000) p is antitone; with K <= 6 the bound on q
keeps its margin. Adds the hypothesis K <= 6 down the stack (unclamping, openness, no-event class, core)."""
import pathlib
P = pathlib.Path(__file__).resolve().parents[1] / 'lean/BlowSep.lean'
s = P.read_text()
def rep(a, b, n=1):
    global s
    assert s.count(a) == n, (a[:70], s.count(a), n); s = s.replace(a, b)
for kname in ('hK0', 'hK'):
    old = f'''    have hH : AntitoneOn (fun s => q s ^ 2 / 2 + p s ^ 3 / 3 - p s) (Icc 0 τ) :=
      anti (g' := fun s => q s * (-(K * cl (max s 0 + 2) (f s) * cl 2 (q s)) + 1 - cl 2 (p s) ^ 2)
          + (p s ^ 2 - 1) * cl 2 (q s))
        (fun η hη => by
          have h1 := ((hq η hη).pow 2).div_const 2
          have h2 := ((hp η hη).pow 3).div_const 3
          have := (h1.add h2).sub (hp η hη)
          exact this.congr_deriv (by push_cast; ring))
        h00 (fun x hx => by
          have hx' : x ∈ Icc 0 τ := ⟨hx.1.le, hx.2.le⟩
          rw [tq x hx', tp x hx']
          obtain ⟨c1, c2, c3, c4, c5, c6⟩ := C x hx'
          have : 0 ≤ K * f x * q x ^ 2 := mul_nonneg (mul_nonneg {kname}.le c5) (sq_nonneg _)
          nlinarith)
    have hq2 : q τ < 2 := by
      have := hH ⟨le_rfl, hτ0⟩ hτI hτ0
      simp only [hp0, hq0] at this
      have hp3 : p τ - p τ ^ 3 / 3 ≤ 2 / 3 := by nlinarith [sq_nonneg (p τ - 1)]
      nlinarith'''
    new = f'''    have hH : AntitoneOn (fun s => q s ^ 2 / 2 + p s ^ 3 / 3 - p s - 2 * K / 1000 * p s) (Icc 0 τ) :=
      anti (g' := fun s => q s * (-(K * cl (max s 0 + 2) (f s) * cl 2 (q s)) + 1 - cl 2 (p s) ^ 2)
          + (p s ^ 2 - 1) * cl 2 (q s) - 2 * K / 1000 * cl 2 (q s))
        (fun η hη => by
          have h1 := ((hq η hη).pow 2).div_const 2
          have h2 := ((hp η hη).pow 3).div_const 3
          have := ((h1.add h2).sub (hp η hη)).sub ((hp η hη).const_mul (2 * K / 1000))
          exact this.congr_deriv (by push_cast; ring))
        h00 (fun x hx => by
          have hx' : x ∈ Icc 0 τ := ⟨hx.1.le, hx.2.le⟩
          rw [tq x hx', tp x hx']
          obtain ⟨c1, c2, c3, c4, c5, c6⟩ := C x hx'
          have hf' : 0 ≤ f x + 1 / 1000 := by linarith [cS_nonneg]
          have e1 : 0 ≤ K * q x ^ 2 * (f x + 1 / 1000) := mul_nonneg (mul_nonneg {kname}.le (sq_nonneg _)) hf'
          have e2 : 0 ≤ K * q x * (2 - q x) := mul_nonneg (mul_nonneg {kname}.le c3) (by linarith)
          nlinarith)
    have hq2 : q τ < 2 := by
      have := hH ⟨le_rfl, hτ0⟩ hτI hτ0
      simp only [hp0, hq0] at this
      have hp3 : p τ - p τ ^ 3 / 3 ≤ 2 / 3 := by nlinarith [sq_nonneg (p τ - 1)]
      have hKp : 2 * K / 1000 * p τ ≤ 12 / 1000 := by nlinarith
      nlinarith'''
    rep(old, new)
rep('theorem unclampS {K : ℝ} (hK5 : 5 ≤ K) {f p q : ℝ → ℝ}', 'theorem unclampS {K : ℝ} (hK5 : 5 ≤ K) (hK6 : K ≤ 6) {f p q : ℝ → ℝ}')
rep('theorem unclampS_neither {K : ℝ} (hK : 0 < K) {f p q : ℝ → ℝ}', 'theorem unclampS_neither {K : ℝ} (hK : 0 < K) (hK6 : K ≤ 6) {f p q : ℝ → ℝ}')
rep('theorem slow_unclamp {K : ℝ} (hK5 : 5 ≤ K) {η₀ : ℝ}', 'theorem slow_unclamp {K : ℝ} (hK5 : 5 ≤ K) (hK6 : K ≤ 6) {η₀ : ℝ}')
rep('  exact unclampS hK5 hF hP hQ', '  exact unclampS hK5 hK6 hF hP hQ')
rep('theorem slowS_open (K₀ : ℝ) (hK₀ : 5 ≤ K₀) (h : SlowS (flowK K₀)) :', 'theorem slowS_open (K₀ : ℝ) (hK₀ : 5 ≤ K₀) (hK₀6 : K₀ ≤ 6) (h : SlowS (flowK K₀)) :')
rep('  have U := slow_unclamp hK₀ hη hpre h1 h2 h3', '  have U := slow_unclamp hK₀ hK₀6 hη hpre h1 h2 h3')
rep('theorem slowS_not_over {K : ℝ} (hK5 : 5 ≤ K) (hS', 'theorem slowS_not_over {K : ℝ} (hK5 : 5 ≤ K) (hK6 : K ≤ 6) (hS')
rep('  have U := slow_unclamp hK5 hη₀ hpre hs1 hs2 hs3\n  obtain ⟨η, hη, hp⟩ := hO', '  have U := slow_unclamp hK5 hK6 hη₀ hpre hs1 hs2 hs3\n  obtain ⟨η, hη, hp⟩ := hO')
rep('theorem neither_class {K : ℝ} (hK : 0 < K) (hnS', 'theorem neither_class {K : ℝ} (hK : 0 < K) (hK6 : K ≤ 6) (hnS')
rep('  have U := unclampS_neither hK hF hP hQ', '  have U := unclampS_neither hK hK6 hF hP hQ')
rep('theorem core_sepS {lo hi : ℝ} (hlo5 : 5 ≤ lo) (hlh : lo < hi) (hO', 'theorem core_sepS {lo hi : ℝ} (hlo5 : 5 ≤ lo) (hlh : lo < hi) (hhi6 : hi ≤ 6) (hO')
rep('slowS_open hi (by linarith) slow_hi', 'slowS_open hi (by linarith) hhi6 slow_hi')
rep('      exact slowS_not_over (by linarith [hK.1.1]) hSK hK.2', '      exact slowS_not_over (by linarith [hK.1.1]) (by linarith [hK.1.2]) hSK hK.2')
rep('    obtain ⟨δ, hδ, hSa\'⟩ := slowS_open a (by linarith) hSa', '    obtain ⟨δ, hδ, hSa\'⟩ := slowS_open a (by linarith) (by linarith) hSa')
rep('    exact slowS_not_over (by linarith [hKS.1.1])', '    exact slowS_not_over (by linarith [hKS.1.1]) (by linarith [hKS.1.2])')
rep('neither_class ha0 hnS hnO', 'neither_class ha0 (by linarith) hnS hnO')
P.write_text(s); print('patched', P)
