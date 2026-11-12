# Referee report: `Work/FalknerSkan/AttachedRows.lean` (run 2026-11-12T1428Z)

Referee: independent Opus subagent (brief in the main session's Agent call; it read only the frozen file and the Guo et al. crop). Its Write call for this file was refused by the harness ("subagents return findings as text"), so the main session saved the hand-back text here verbatim in substance. Scripts and logs written by the referee: `scripts/fs_mp.py`, `scripts/fs_bvp.py`, `scripts/fs_extra.py`, `logs/`; typeset crops `typeset/ganapol2010_p19_table5.png`, `typeset/ganapol2010_p21_table6_rows.png`.

**Verdict: STANDS-WITH-CORRECTIONS.** All ten frozen statements (five windows, five existence statements; row −0.17 was added after this report) are correct; every window contains the true f''(0) of the attached branch. Correction only to the module docstring's novelty sentence (−0.19 is in print; cite Ganapol for −0.15 and −0.18). No theorem changes.

## 1. Independent values
Far-field condition: neither method uses f'(L) = 1. Both impose the asymptotic Robin condition f''(L) = R(f(L))·(1 − f'(L)), R = D_{ν+1}/D_ν, ν = −1 − 2β (keeps the fast-decaying mode e^{−ξ²/4}D_ν(ξ) of the linearised tail g'' + ξg' − 2βg = 0, g = 1 − f'; removes the algebraic mode ξ^{2β}).
- Method A: mpmath, 40 digits, own Taylor-series integrator; (order 40, h = 0.125) and (order 30, h = 0.2); L = 10, 12, 14, 16; secant on s = f''(0). All agree to 25 digits. Plain f'(L) = 1 shooting visibly wrong at L = 6 (0.2163771 at β = −0.15), converges only for L ≥ 14.
- Method B: scipy `solve_bvp` collocation, same boundary condition, L = 8–14; agrees with A to ≈ 1e-15.

| β | f''(0) (method A) | window | inside | lower margin | upper margin |
|---|---|---|---|---|---|
| −0.15 | 0.21636140564711143644 | (0.2163614056, 0.2163614057) | yes | 4.71e-11 | 5.29e-11 |
| −0.18 | 0.12863622059606084622 | (0.1286362205, 0.1286362206) | yes | 9.61e-11 | 3.94e-12 |
| −0.19 | 0.085699744059816832427 | (0.0856997440, 0.0856997441) | yes | 5.98e-11 | 4.02e-11 |
| −0.195 | 0.055171828577137654755 | (0.0551718285, 0.0551718286) | yes | 7.71e-11 | 2.29e-11 |
| −0.198 | 0.025094283620864466258 | (0.0250942836, 0.0250942837) | yes | 2.09e-11 | 7.91e-11 |

Extra: β = −0.1988 gives 0.0052181878839093. Reversed (Stewartson) branch at the five rows: −0.133421237895, −0.0976920601346, −0.0713359060034, −0.0489670821290, −0.0237440897202 (first three match Ganapol Table 7 to all 12 printed digits).

## 2. Statement check
- `hq` is q' = −fq − β(1 − p²), i.e. f''' + ff'' + β(1 − f'²) = 0; β literals correct. `HasDerivWithinAt` on `Ici 0`: one-sided at 0, values on (−∞, 0) irrelevant. No division, decimal literals are exact rationals. Existence theorems use exactly the window theorems' hypotheses (not vacuous).
- `hpos` (q > 0) excludes the reversed branch. With q > 0 and p → 1, p < 1 everywhere, so `hdec` says exactly q/(1 − p) → ∞: the fast-decaying (Hartree) solution meets it (q/(1 − p) ~ ξ), the algebraic mode fails it (q/(1 − p) ~ −2β/ξ → 0).
- `hdec` is essential: shots from s* − 1e-3 and s* − 1e-6 give f'' > 0 on [0, 200] with f' → 1 algebraically (f''/(1 − f') ≈ 1.5e-3 to 2.0e-3 ≈ −2β/η): a continuum of attached solutions meeting every hypothesis but `hdec`. Shots from s* + δ overshoot to f' > 1 and hit f'' = 0 (`hpos` excludes them). `hlim` harmless. Nothing vacuous or trivially satisfied found.

## 3. Printed values
| Source | how read | β | printed | correctly rounded? |
|---|---|---|---|---|
| Guo et al., arXiv:2010.05682v1, Table 8, Jaya column | typeset PNG | −0.15 / −0.18 / −0.1988 | 0.216361 / 0.128636 / 0.005218 | yes / yes / yes |
| same table, columns "Zhang [35]", "Asaithambi [4]" | typeset PNG | −0.15 / −0.18 / −0.1988 | 0.21636 / 0.12863 / 0.00522 | yes / **no** (0.12864; looks truncated) / yes |
| same table, PSO / Hyperband / GA | typeset PNG | −0.18 | 0.12864 / 0.13208 / 0.12884 | yes / no / no |
| same table, PSO / Hyperband / GA | typeset PNG | −0.1988 | 0.00559 / 0.00509 / 0.00513 | all wrong |
| Ganapol, arXiv:1006.3888v1, Table 5, p. 19 | rendered 200 dpi, crop | −0.15 / −0.18 | "2.16361405647" / "1.28636220596" | digits right (12 sig.), table drops the ×10⁻¹ exponent |
| same, Table 5 | rendered, crop | −0.1988 | 5.218187884E-03 | yes |
| Ganapol, Table 6 ("Comparison to Katagiri"), p. 21 | rendered, crop | −0.15 / −0.18 | 2.16361405647E-01 / 1.28636220596E-01 | yes (12 sig.) |
| same, Table 6 | rendered, crop | −0.19 | 8.56997440597E-02 | 12th digit off by one (…598; error 1.2e-13) |
| Balaji et al., arXiv:2008.01671v1 | text extraction only, normalisation not checked | −0.1988 | 0.00521828 | no (0.00521819) |

Not read: Katagiri 1985 (Ganapol: 10–11 digits for −0.19 ≤ β ≤ 1); originals of Zhang & Chen 2009, Asaithambi 2005, Salama 2004 (Ganapol's Table 4b says Asaithambi's last digit disagrees at −0.18 and Salama's at −0.15 and −0.18); Hartree, Smith, Cebeci & Keller, Cebeci & Bradshaw, White, Fazio. No printed value at −0.195 or −0.198 found (web search and six other arXiv papers' text).

**Novelty:** −0.15, −0.18, −0.19 are in print to 12 digits (Ganapol 2010): those windows are confirmations. −0.195 and −0.198 appear new.

## 4. Mapping to Hartree's m-form
m = β/(2 − β), f_m''(0) = f''(0)/√(2 − β): −0.15 → m = −0.0697674419, 0.147557253931; −0.18 → −0.0825688073, 0.0871234420293; −0.19 → −0.0867579909, 0.0579105203805; −0.195 → −0.0888382688, 0.0372391805604; −0.198 → −0.0900818926, 0.0169262580688. No round m, so no m-form table holds these rows; no other tabulated family gives more digits.
