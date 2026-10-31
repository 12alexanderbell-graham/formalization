import sys, pathlib
root = pathlib.Path(sys.argv[1])
p = root / "Checked/Cosmography/Lookback.lean"
s = p.read_text(encoding="utf-8")
def rep(old, new):
    global s
    assert s.count(old) == 1, (old, s.count(old))
    s = s.replace(old, new)
# keep the real proof under a helper name
rep("theorem lookback_second_order (a : ℝ → ℝ) (t₀ : ℝ)\n",
    "theorem lookback_second_order_aux (a : ℝ → ℝ) (t₀ : ℝ)\n")
rep("  exact hL_o.trans_isBigO (hzO.pow 2)\n\nend Checked.Cosmography\n",
"""  exact hL_o.trans_isBigO (hzO.pow 2)

/-- **Milestone 1, restated in big-O form.** The lookback time `t₀ - t` of a source with redshift
`z = z(t)` is given to second order in `z` by the cosmographic series
`t₀ - t = H₀⁻¹ (z - (1 ∓ q₀/2) z²) + O(z²)` as `t → t₀` (Peano remainder in `lookback_second_order_aux`). -/
theorem lookback_second_order (a : ℝ → ℝ) (t₀ : ℝ)
    (ha : ∀ᶠ t in 𝓝 t₀, DifferentiableAt ℝ a t)
    (ha' : DifferentiableAt ℝ (deriv a) t₀)
    (ha0 : a t₀ ≠ 0) (hH : deriv a t₀ ≠ 0) :
    (fun t => (t₀ - t) - (redshift a t₀ t - (1 - decel a t₀ / 2) * redshift a t₀ t ^ 2)
        / hubble a t₀)
      =O[𝓝 t₀] (fun t => redshift a t₀ t ^ 2) := by
  have h1 := (lookback_second_order_aux a t₀ ha ha' ha0 hH).isBigO
  have h2 : (fun t => decel a t₀ / hubble a t₀ * redshift a t₀ t ^ 2)
      =O[𝓝 t₀] (fun t => redshift a t₀ t ^ 2) :=
    isBigO_const_mul_self (decel a t₀ / hubble a t₀) (fun t => redshift a t₀ t ^ 2) _
  have e : (fun t => (t₀ - t) - (redshift a t₀ t - (1 - decel a t₀ / 2) * redshift a t₀ t ^ 2)
        / hubble a t₀) = fun t =>
      ((t₀ - t) - (redshift a t₀ t - (1 + decel a t₀ / 2) * redshift a t₀ t ^ 2)
        / hubble a t₀) - decel a t₀ / hubble a t₀ * redshift a t₀ t ^ 2 := by
    funext t; ring
  rw [e]
  exact h1.sub h2

end Checked.Cosmography
""")
p.write_text(s, encoding="utf-8")
