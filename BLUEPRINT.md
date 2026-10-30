# BLUEPRINT

Target 1: cosmographic (low-redshift) expansions. Nodes with statuses (annex XXXVIII). Mathlib-only; definitions mirror Physlib's.

- `peano2` (Peano 2nd-order Taylor at a point, a differentiable near, a′ differentiable at t₀): PROVED (helper, Checked).
- `peano3` (3rd order): PROVED in Work (helper; copy in Checked).
- M1 `lookback_second_order` (o(z²)): **PROVED** (Checked, AUDITED).
- M1b `lookback_second_order_bigO` (O(z³), C³): **PROVED** (Checked, AUDITED).
- M2 d_L = (c/H₀)[z + ½(1 − q₀)z² + o(z²)], needs χ = c∫dt/a expansion and r = S_k(χ): not started.
- M3 d_L z³ coefficient −(1/6)[1 − q₀ − 3q₀² + j₀ + kc²/(H₀²a₀²)] (curvature enters): not started.
- M4 general machinery for order n (series composition/inversion), needed to certify z⁴–z⁵ coefficients and the screen candidates C1–C4: not started.
- F1 (was C2) `flatLCDM_coeffs`, `avilesL0Claim_false`, `avilesM0Claim_false`, `printedL0_false_at`, `printedM0_false_at`: **PROVED** (Checked, AUDITED). Method reusable: polynomial Friedmann identity, repeated `step`, generated certificates.
- C4 CPL l₀ (needs: same method with H(a) containing a^{−3(1+w₀+w_a)} e^{−3w_a(1−a)}; witness model existence is harder (no closed form), so state the correct value as a theorem conditional on a model, and refute the printed value via `flatLCDM`-style witness only if an explicit CPL solution is found, or via Picard–Lindelöf existence): not started.
- C3 refutation on de Sitter (lookback distance D(z) = (c/H₀)ln(1+z); printed D_z⁴ at q=−1, j=s=l=1 gives 2.825 ≠ 1/5): needs a z⁵-order statement about ln(1+z); not started.
- C1 refutation (d_Q(y) y² coefficient): needs d_L to O(z³) (M3) or an explicit model; not started.
