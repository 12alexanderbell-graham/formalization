# Blind second formulation B (cosmography series coefficients) — run 2026-11-05T0828Z

You derive, independently, Taylor coefficients of cosmological distance–redshift series and write
them as Lean 4 definitions. Another program wrote definitions with the same names; a machine will
check (by unfolding and `ring`) whether yours equal theirs. You must NOT read theirs.

**Do not read** anything under `/home/claude/formalization/Checked` (EXCEPT the files
`Checked/Trust/SecondReading.lean` and `Checked/Trust/SecondReadingFR.lean`, which you may read
and use), `/home/claude/formalization/Work`, `/home/claude/formalization/runs` (except this brief),
`/home/claude/formalization/scripts`, or any `*.md` file of the repository. Do not grep the
repository for these names. Use Python/sympy for every derivation (scratch under `/tmp/blindB/`;
keep your derivation script and copy it to
`/home/claude/formalization/runs/2026-11-05T0828Z/blind/derive_cosmo.py` at the end). Lean:
`cd /home/claude/formalization && source ~/.elan/env && lake env lean <file>` (a background build
is running; if `Checked.Trust.SecondReading` is not built yet, wait a few minutes and retry, or
compile a copy without that import to check syntax).

Write exactly one file: `/home/claude/formalization/runs/2026-11-05T0828Z/blind/SecondFormulationCosmo.lean`:

```lean
import Mathlib.Data.Real.Basic
import Checked.Trust.SecondReading
import Checked.Trust.SecondReadingFR
namespace Checked.Trust.SecondFormulation
...
end Checked.Trust.SecondFormulation
```

Every definition gets a docstring stating the quantity and "derived by sympy in derive_cosmo.py".
The file must compile with no `sorry`. Write each coefficient as the FULL polynomial you derived
(do not express it as "printed + correction"; you do not know the printed values except where a
SecondReading constant is named below).

## Conventions (all at t = t₀; c = 1)

a(t) scale factor (smooth, positive), a₀ = a(t₀). H = ȧ/a, H₀ = H(t₀) > 0.
q₀ = −ä a/ȧ², j₀ = a⃛/(a H³), s₀ = a⁽⁴⁾/(a H⁴), l₀ = a⁽⁵⁾/(a H⁵) (Lean arguments `q j s l`).
Redshift z = a₀/a(t) − 1 (t < t₀ in the past); y = z/(1 + z).
Comoving distance χ = ∫_t^{t₀} dt'/a(t'). Curvature constant K of the FLRW metric; transverse
distance S_K(χ) = sin(√K χ)/√K (K > 0), χ (K = 0), sinh(√−K χ)/√−K (K < 0).
Luminosity distance d_L = a₀ (1 + z) S_K(χ). Angular-diameter distance d_A = d_L/(1 + z)².
Curvature parameters used as arguments: `Ω` means Ω₀ = 1 + K/(H₀² a₀²) (so Ω = 1 is flat; NOTE
the sign: this Ω is 1 − Ω_k in the usual notation); `k` means K/(H₀² a₀²).
"Coefficient Dⁿ of X in z" means: H₀·X = z [1 + D¹ z + D² z² + D³ z³ + D⁴ z⁴ + …] (Taylor series
of H₀·X as a function of z near 0, divided by z); likewise in y.

## The definitions (exact names and argument order)

1. `correctD4 (q j s l : ℝ) : ℝ` — the z⁴ coefficient D⁴ of the LOOKBACK TIME t₀ − t in z:
   H₀ (t₀ − t) = z[1 + D¹z + D²z² + D³z³ + D⁴z⁴ + …].
2. `series (d4 q j s z : ℝ) : ℝ` — the truncated lookback series z(1 + D¹z + D²z² + D³z³ + d4·z⁴)
   where D¹, D², D³ are the values PRINTED in the source: `Checked.Trust.SecondReading.D1 q`,
   `Checked.Trust.SecondReading.D2 q j`, `Checked.Trust.SecondReading.D3 q j s`.
3. `correctD2y (q j Ω : ℝ) : ℝ` — the y² coefficient of d_L in y (curved, Ω as above).
4. `seriesY (d2 q y : ℝ) : ℝ` — y(1 + D¹y + d2·y²) with D¹ the printed
   `Checked.Trust.SecondReading.D1y q`.
5. `correctD3y (q j s Ω : ℝ) : ℝ`, 6. `correctD4y (q j s l Ω : ℝ) : ℝ` — the y³ and y⁴ coefficients
   of d_L in y (curved).
7. `seriesY4 (q d2 d3 d4 y : ℝ) : ℝ` — y(1 + D¹y + d2 y² + d3 y³ + d4 y⁴), D¹ =
   `Checked.Trust.SecondReading.D1y q`.
8. `correctDA3 (q j s Ω : ℝ) : ℝ`, 9. `correctDA4 (q j s l Ω : ℝ) : ℝ` — the y³ and y⁴
   coefficients of d_A in y (curved).
10. `correctDL4z (q j s l k : ℝ) : ℝ`, 11. `correctDA4z (q j s l k : ℝ) : ℝ` — the z⁴ coefficients
    of d_L and of d_A in z (curved, k as above).
12. `seriesZ (d1 d2 d3 d4 z : ℝ) : ℝ` — z(1 + d1 z + d2 z² + d3 z³ + d4 z⁴).
13. `correctQ2 (q j Ω : ℝ) : ℝ` — the y² coefficient of the "deceleration distance"
    d_Q = d_L/(1 + z)^{3/2} in y (curved, Ω as above).
14. `seriesQ (d2 q y : ℝ) : ℝ` — y(1 − (q/2)·y + d2·y²).
15. `correct20 (Ω : ℝ) : ℝ`, 16. `correct30 (Ω : ℝ) : ℝ` — F(R)-gravity ratios on a one-parameter
    family. Define, with `P0 P2 P3 Q0 Q2 Q3` the constants of `Checked.Trust.SecondReading`
    (read `SecondReadingFR.lean` for their argument order),
    η₂₀(q,j,s,l) = (P2·Ω + Q2)/(36·(P0·Ω + Q0)) and
    η₃₀(q,j,s,l) = (P3·Ω + Q3)/(216·(j − q − 2)·(P0·Ω + Q0)),
    and the family q = q_Λ(1+ε), j = 1·(1+ε), s = s_Λ(1+ε), l = l_Λ(1+ε) with the ΛCDM values
    q_Λ = 3Ω/2 − 1, s_Λ = 1 − 9Ω/2, l_Λ = 1 + 3Ω + 27Ω²/2. `correct20 Ω` / `correct30 Ω` is the
    derivative with respect to ε at ε = 0 of η₂₀ / η₃₀ on this family (both vanish at ε = 0;
    check that). Simplify to a single rational function of Ω (sympy `factor`) and write it as one
    fraction.

Verify every coefficient numerically on at least two exact models (e.g. de Sitter a = e^{t}:
q = −1, j = s = l = 1; a matter-dominated or Milne model; a curved model with known d_L) before
writing it. At the end reply with: the file path, the models you checked, and any item where you
were unsure of the convention.
