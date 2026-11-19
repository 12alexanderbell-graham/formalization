# Referee brief: Work/Math/LaneEmden4.lean (laneEmden4_constants)

You are a hostile referee. Read `Work/Math/LaneEmden4.lean` (the frozen statement; the proof is `sorry`). Do not read other Lean files of the repository. Write your report to `runs/2026-11-19T0428Z/referee/REPORT.md` (only that file), with a first line `Verdict: STANDS` or `Verdict: FALLS` (with the reason).

1. Attack the statement: is it satisfiable (the true regular solution of θ'' + (2/ξ)θ' + θ⁴ = 0, θ(0) = 1, exists on [0, 16] without blow-up?), are the hypotheses strong enough to force the classical solution (θ'(0) = 0 is not assumed: is it implied?), junk values (division by zero, Lean's real division, the one-sided derivatives at the ends of the interval), quantifiers, whether "first zero" is captured, whether anything makes it trivial or vacuous.
2. Compute independently (mpmath or your own Taylor integrator, at least 30 digits, two methods that you compare) ξ₁, ω₄ = −ξ₁² θ'(ξ₁) and ξ₁³/(3ω₄), and report the margins of every printed bound (value − lower end, upper end − value). A bound that your computation contradicts makes the statement FALL.
3. Compare with the classical tables (Chandrasekhar 1939; Horedt 1986) from your own knowledge only (no web), stating which digits you remember.
