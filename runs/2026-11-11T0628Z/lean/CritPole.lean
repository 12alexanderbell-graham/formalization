import Checked.Trust.NecessityB

open Set Filter Topology

namespace Checked.Trust.NCD

/-- A pole of the isotherm beyond the covolume is a (junk) critical point for every temperature
(`NCB.crit_at_root`), so the critical point is not unique. -/
theorem not_unique_of_pole (R a b u w v₀ : ℝ) (hb : b < v₀) (ha : a ≠ 0)
    (hD : v₀ ^ 2 + u * b * v₀ + w * b ^ 2 = 0)
    (hne : ∀ᶠ x in 𝓝[>] v₀, x ^ 2 + u * b * x + w * b ^ 2 ≠ 0) :
    ¬ ∃! p : ℝ × ℝ, 0 < p.1 ∧ b < p.2 ∧
      Checked.Chemistry.CubicEOS.IsCriticalIsotherm (Checked.Chemistry.CubicEOS.cubicP R a b u w p.1) p.2 := by
  rintro ⟨p, -, hp⟩
  have h1 := hp (1, v₀) ⟨one_pos, hb, NCB.crit_at_root R a b u w 1 v₀ hb ha hD hne⟩
  have h2 := hp (2, v₀) ⟨two_pos, hb, NCB.crit_at_root R a b u w 2 v₀ hb ha hD hne⟩
  have := congrArg Prod.fst (h1.trans h2.symm)
  norm_num at this

/-- `0 < b` is needed in `CubicEOS.exists_unique_critical`: with `b = 0` (`R = a = 1`, `u = w = 0`)
the critical conditions force `v³ = 0`, impossible for `v > 0`. -/
theorem exists_unique_critical_h3 :
    necessity% Checked.Chemistry.CubicEOS.exists_unique_critical 3 := by
  refine ⟨1, 1, 0, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  rintro ⟨p, ⟨hT, hv, hc⟩, -⟩
  have hD : 0 < p.2 ^ 2 + 0 * 0 * p.2 + 0 * 0 ^ 2 := by nlinarith
  have := ((Checked.Chemistry.CubicEOS.isCritical_iff 1 1 0 0 0 p.1 p.2 one_pos hv hD).1 hc).1
  have : p.2 ^ 3 = 0 := by linarith
  have := pow_eq_zero_iff (n := 3) (by norm_num) |>.1 this
  linarith

/-- `−2 < u` is needed in `CubicEOS.exists_unique_critical`: at `u = −3`, `w = 9/4` (`1 + u + w = 1/4`,
`R = a = b = 1`) the isotherm has a pole at `v = 3/2` beyond the covolume, a junk critical point at
every temperature. -/
theorem exists_unique_critical_h4 :
    necessity% Checked.Chemistry.CubicEOS.exists_unique_critical 4 := by
  refine ⟨1, 1, 1, -3, 9 / 4, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  refine not_unique_of_pole 1 1 1 (-3) (9 / 4) (3 / 2) (by norm_num) one_ne_zero (by norm_num) ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : (3 : ℝ) / 2 < x := hx
  nlinarith

/-- `0 < 1 + u + w` is needed in `CubicEOS.exists_unique_critical`: at `u = 0`, `w = −4`
(`R = a = b = 1`) the isotherm has a pole at `v = 2` beyond the covolume. -/
theorem exists_unique_critical_h5 :
    necessity% Checked.Chemistry.CubicEOS.exists_unique_critical 5 := by
  refine ⟨1, 1, 1, 0, -4, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  refine not_unique_of_pole 1 1 1 0 (-4) 2 (by norm_num) one_ne_zero (by norm_num) ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : (2 : ℝ) < x := hx
  nlinarith

end Checked.Trust.NCD
