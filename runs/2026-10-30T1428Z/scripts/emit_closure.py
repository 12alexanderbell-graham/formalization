"""Emit the statement of `closure` (generic H-derivatives) for FRCosmo.lean."""
h=['hubble a t₀']+[f'deriv^[{k}] (hubble a) t₀' for k in range(1,5)]
H=h[0]; h1,h2,h3,h4=[f'({x})' for x in h[1:]]
R0=f'(-6 * ({h1} + 2 * {H} ^ 2))'; R1=f'(-6 * ({h2} + 4 * {H} * {h1}))'
R2=f'(-6 * ({h3} + 4 * {h1} ^ 2 + 4 * {H} * {h2}))'; R3=f'(-6 * ({h4} + 12 * {h1} * {h2} + 4 * {H} * {h3}))'
x0='F (curv a t₀)'; x2='deriv^[2] F (curv a t₀)'; x3='deriv^[3] F (curv a t₀)'
E1=f'3 * {H} ^ 2 = 3 * {H} ^ 2 * Ω + ({x0} - {R0}) / 2 - 3 * {H} * {R1} * {x2}'
E2=f'-2 * {h1} = 3 * {H} ^ 2 * Ω + {R2} * {x2} + {R1} * ({R1} * {x3} - {H} * {x2})'
E3=(f'-2 * {x2} * {R1} * {h1} - 2 * {h2} = -3 * {H} * (3 * {H} ^ 2 * Ω) + {R3} * {x2}'
    f' + 3 * {R1} * {R2} * {x3} - {h1} * {R1} * {x2} - {H} * {R2} * {x2} - {H} * {R1} ^ 2 * {x3}')
print(f"""/-- The closure system at `t₀`: (11.14), (11.15) and the time derivative of (11.5) ((11.20),
with the correct `−Ḣ₀Ṙ₀`), using `F′(R₀) = 1`, `F⁽⁴⁾(R₀) = 0`. -/
lemma closure (Ω : ℝ) (a F : ℝ → ℝ) (t₀ : ℝ) (hM : IsFRCosmo Ω a F t₀) :
    ({E1}) ∧
    ({E2}) ∧
    ({E3}) := by
  sorry
""")
