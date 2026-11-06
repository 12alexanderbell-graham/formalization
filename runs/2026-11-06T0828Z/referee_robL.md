# Referee report: Work/Sim/RobLong.lean (run 2026-11-06T0828Z)

## 1. Statement fidelity
- `IsRobSolution (1/25) 10⁴ (3·10⁷) 1 0 0 10¹¹`: all constants are exact literals, there are no junk divisions, and the evaluation at 10¹¹ lies inside [0, T]. Derivatives within Icc imply continuity, and the field is polynomial, so the solution is unique. No positivity or boundedness hypothesis is needed: the proof confines the solution to the box by itself (`chain` up to t = 40, then `stepS`), and conservation gives y₁ = 1 − y₂ − y₃. Restricting from T = 10¹¹ to T = 40 works through `mono`.
- Vacuity: `rob_state1e11` and `rob_printed_y3_false` are vacuous until `rob_exists_1e11` is proved. That theorem is stated correctly. It still has `sorry`, but the route is credible (`RobExistsLong` plus the box from the cells, as was done for `rob_exists` at t = 40).
- The docstring intervals match the literals. "Ten significant digits" for y₁ holds only by truncation: the interval contains values whose first ten digits round to 2.083340149 and others that round to …150. The module doc says "77 cells", which matches RobLCerts0–7 (77 `stepL`, final radius 7/5·10⁻¹⁸). The commit message says "113 cells, 7.6e-21"; that is a different generator run, so the record should state which run is used.
- **`rob_printed_y3_false` overclaims.** `y₃ ≠ 0.9999999791665050` would equally hold for the correctly rounded value 0.9999999791665152, so the ≠ form tells us nothing. The real content is the frozen interval: the printed value lies at least 5.0·10⁻¹⁵ below the true y₃. More seriously, the asymmetry is an artefact of interval width. All three printed components have **relative error of about 10⁻¹⁴** (my digits): y₁ −1.9·10⁻¹⁴, y₂ −8.4·10⁻¹⁵, y₃ −1.0·10⁻¹⁴. y₁ is "inside" only because its frozen interval is 3·10⁻¹⁰ wide relative to its value. The test set scores codes by relative error (scd), so its reference is uniformly good to about 14 digits. What it gets wrong is printing 16 digits. Calling y₃ alone "false" is misleading.

## 2. Independent numerics (in /tmp/claude-0/referee/)
I wrote my own Radau IIA (s = 5 and s = 7) in mpmath at 50–60 digits. It runs in s = ln(1 + t/10⁻⁵) with uniform steps and integrates (y₁, y₂), with y₃ = 1 − y₁ − y₂. With s = 7 and 737 steps:

- y₁ = 2.08334014970129423057·10⁻⁸
- y₂ = 8.3333607703347834006·10⁻¹⁴
- y₃ = 0.99999997916651516937935435

Convergence checks:
- s = 5 at 369 and at 737 steps agree with each other and with s = 7 to 22, 20 and 26 digits respectively.
- scipy Radau at rtol 1e−13 agrees to about 13 digits. LSODA and BDF agree to 10 or more.

All three values lie inside the frozen intervals. The emitter's final ball (centre n₂, n₃; radius 1.4·10⁻¹⁸; c ≈ 4·10⁻⁴) contains them, with margins after the radius of y₁ ≥ 1.45·10⁻¹⁸, y₂ ≥ 2.5·10⁻¹⁹ and y₃ ≥ 4.8·10⁻¹⁵. The y₁ margin is tight but positive. On the printed values in exact decimal arithmetic, 1 − Σ = 1.0169·10⁻¹⁴, and true y₃ minus printed y₃ = 1.01694·10⁻¹⁴ (about 92 units of 2⁻⁵³). So the printed y₃ is inconsistent with the certified interval and with y₁ + y₂ + y₃ = 1, as claimed.

## 3. Method
- `shear_onesided`: Φ is quadratic in (u, k). Its coefficients Al, Be and Ga are each affine in x₂, x₃ and h₂ (Φ_x2, Φ_x3, Φ_h2 are proved). Interpolating one variable at a time over the eight corners is valid. CornerOK (P > 0 and Q² ≤ 4PR) is the correct PSD criterion. Specialising to u = d·h₂ after the bound is legitimate, because the bound holds for all (u, k). The identity `e` is closed by `field_simp; ring`. The sheared field (P, Q + cP) in coordinates (y₂, y₃ + c y₂) is correct.
- `cellS` and `stepS` are sound: `onesided_cell_neg` is a standard comparison with radius δe^{μs} + εs for μ ≤ 0. The end radius uses e^{μh} ≤ 1/(1 − μh), the change of shear `shear_switch` is correct, and `start_shear` matches the emitter's Δ₀.
- `cheb_bound`: Clenshaw evaluation is proved to equal Σ bₖTₖ, |Tₖ| ≤ 1 on [−1, 1], and the rescaling is correct.
- None of RobShear, ChebBound or OneSidedNeg contains `sorry`, and their .olean files exist.
- Generator vs Lean: every `stepS` hypothesis is re-proved in Lean by `decide +kernel` or `norm_num` (Chebyshev equalities, sumAbs bounds, corners, hbox with B + |c|B/d, δ, Rend, Δ′), so the Python code is not trusted. One gap: gen_robL.py's own box test omits the |c|B/d term, but emit_robL.py checks the correct one. The real outstanding risk is that only RobLCerts0 has been built. Cells 1–76, the final assembly and existence are unproven.

## 4. Prior art
I spot-checked arXiv:2407.04008 (Baumgartner & Szmolyan, asymptotic GSPT for Robertson, not rigorous), arXiv:2607.01189 (TERA Taylor-model reachability, no Robertson), arXiv:2206.13873 (DDEs) and van der Hoeven 2018 (high-precision stiff ball integration, no Robertson). None gives a rigorous ROBER enclosure at t ≥ 10³, and none documents the reference-value error. This agrees with the screen. Novelty is real but modest: it is the first certified long-horizon enclosure, together with the observation that the printed reference is accurate to about 14, not 16, digits.

## Verdict: STANDS-WITH-CORRECTIONS
1. Rewrite the `rob_printed_y3_false` docstring and the module prose. Drop "is false". Say instead that the printed y₃ differs from the true value by more than 5·10⁻¹⁵ (in fact 1.017·10⁻¹⁴) and violates conservation. Also say that the printed y₁ and y₂ carry relative errors of the same order (about 10⁻¹⁴) and lie inside only because their intervals are wider. Optionally replace the ≠ statement with `1/(2·10¹⁴) < y₃(10¹¹) − 0.9999999791665050`.
2. Change "ten significant digits" to "first ten significant digits 2.083340149".
3. Make the run record agree on the cell count and radius (77 cells and 1.4·10⁻¹⁸, not 113 and 7.6·10⁻²¹).
4. Do not report the result as established until RobLCerts1–7, `rob_state1e11` and `rob_exists_1e11` build without `sorry`.
