# Referee report: Work/FalknerSkan/AttachedRowsTop.lean (frozen 67f8eef), run 2026-11-13T1640Z

Referee: independent Opus subagent (≈ 12 min). Its Write to this path was refused by the harness, so the main session copied its hand-back here verbatim in substance (tables and conclusions unchanged); its scripts and logs are in `scripts/` and `logs/` next to this file.

**Verdict: STANDS.** All six statements (three windows β = −0.13, −0.14, −0.16 and three existence statements) are correctly posed; every window strictly contains the true f''(0) of the attached branch, by at least 1.18e-11. No theorem or docstring changes needed.

## 1. Independent values
Both methods impose the asymptotic Robin condition f''(L) = R·(1 − f'(L)), R = D_{ν+1}(ξ)/D_ν(ξ), ν = −1 − 2β, ξ = f(L) (derived by the referee: g = 1 − f' satisfies g'' + f g' − 2βg = 0, Weber's equation under g = e^{−ξ²/4}h; the condition removes the algebraic mode ξ^{2β}).
- Method A (mpmath, 40 digits, own Taylor integrator + secant shooting): (L, h, order) = (10, .125, 40), (12, .2, 30), (14, .125, 40), (16, .2, 30) agree to 28 digits.
- Method B (scipy solve_bvp, tol 1e-11): Robin at L = 8–14 agrees with A to 1e-16–1e-15; plain f'(L) = 1 at L = 10–25 to ≤ 3e-15.

| β | f''(0) (method A) | window | inside? | lower margin | upper margin |
|---|---|---|---|---|---|
| −0.13 | 0.2614227559871148569137964211 | (0.2614227559, 0.2614227560) | yes | 8.71e-11 | 1.29e-11 |
| −0.14 | 0.2397359553117654234931917554 | (0.2397359553, 0.2397359554) | yes | 1.18e-11 | 8.82e-11 |
| −0.16 | 0.1907798552686704349759783275 | (0.1907798552, 0.1907798553) | yes | 6.87e-11 | 3.13e-11 |

## 2. Ganapol Table 6 (crop `runs/2026-11-12T1428Z/referee/typeset/ganapol2010_p21_table6_rows.png`)
| β | printed α | correctly rounded to 12 sig.? | printed − true |
|---|---|---|---|
| −0.13 | 2.61422755987E-01 | yes | −1.15e-13 |
| −0.14 | 2.39735955312E-01 | yes | +2.35e-13 |
| −0.16 | 1.90779855269E-01 | yes | +3.30e-13 |

## 3. Attack
- Encoding: hq is q' = −fq − β(1 − p²); β literals exact; decimal bounds exact rationals; one-sided derivatives at 0; no junk-value source.
- Quantifiers: windows universal over the class; each existence statement has exactly the window's hypotheses (non-vacuous); hypotheses alone do not fix q(0) (not trivial).
- hpos + hlim force p strictly increasing to 1; hdec is then exactly q/(1 − p) → ∞ (Hartree solution: grows like ξ).
- **hdec is essential**: shots s ∈ {1e-4, 0.01, 0.05, 0.1, s*/2, s* − 1e-2, …} give q > 0 on [0, 300], p < 1, p → 1 algebraically with q/(1 − p) ≈ −2β/η → 0 (`logs/scan.log`): a continuum of solutions meeting every other hypothesis with q(0) anywhere in (0, s*).
- Shots above s* overshoot (p > 1, q reaches 0 at η ≈ 4–8.7): excluded by hpos; the reversed branch has q(0) < 0: excluded by hpos.
- Uniqueness in the class: numerically {s*}, the switch sharp to 1e-9 in s; plausible (Coppel).

## 4. Prior art
All three values are in print to 12 digits in Ganapol 2010 Table 6 ("Comparison to Katagiri Results"; Katagiri 1985, Tokyo Symposium on Mechanics for Space Flight, ADS abstract only: ten-decimal accuracy claimed). The qualitative answer is classical. The windows confirm published numbers; no novelty claim is made. Sources: arXiv:1907.09912 read (no values at these β); arxiv.org/pdf/1006.3888 and /abs not read (permission timed out / blocked; not retried); Katagiri full text, Asaithambi 2005, Zhang & Chen 2009, Cebeci & Keller not read.
