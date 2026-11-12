# Referee report (run 2026-11-12T0427Z; Opus subagent; saved by the main session — the subagent was told to return findings as text)

**Verdict: STANDS.** `bonnor_ebert_critical` (runs/2026-11-12T0427Z/lean/BonnorEbert.lean) formalizes the Bonnor–Ebert critical state correctly; not vacuous; hypotheses fix the solution uniquely; every window contains the true value; smallest margin 1.15e-8.

## 1. Attacks
- Sign: Emden ψ'' + (2/ξ)ψ' = e^{−ψ}, ρ = ρ_c e^{−ψ}; w = −ψ gives w'' + (2/ξ)w' + e^w = 0; `hφ` matches.
- Mass: M = 4πρ_c (c²/4πGρ_c)^{3/2} ξ²ψ' with P_ext = ρ_c c² e^{−ψ(ξ)} gives M = c⁴G^{−3/2}P^{−1/2} · ξ²ψ'e^{−ψ/2}/√(4π). Cross-check R_BE = ξ₁e^{−ψ/2}/√(4π) · c/√(Gρ₀) = 0.4856 c/√(Gρ₀) (McKee & Ostriker print 0.486).
- Contrast e^{−w} correct; w strictly decreasing, so first maximum in ξ = first maximum in contrast.
- Junk solutions / uniqueness: (s²φ)' = −s²e^w on (0, S]; φ continuous at 0 ⇒ ε²φ(ε) → 0 ⇒ s²φ(s) = −∫₀ˢ t²e^w ⇒ φ(0) = 0; integral equation contraction near 0 ⇒ unique. `Ioc` excludes 2/s at 0; values outside [0, S] never enter.
- Existence: global, w ≤ 0, |w'| ≤ s/3 ⇒ hypotheses satisfiable for every S ≥ 7.
- Quantifiers: StrictMonoOn [0, ξ₁] + StrictAntiOn [ξ₁, 7] make ξ₁ the unique peak on [0, 7]; windows are real claims.
- Right end 7: dm/dξ < 0 on (ξ₁, 7] (largest grid value on [6.46, 7] −8.8e-5, at 7: −4.07e-3); m(7) = 1.178245. Next zero of dm/dξ ≈ 67.02 (a minimum, m ≈ 0.69437, contrast ≈ 2580.6).

## 2. Independent computation (scripts `scripts/be_taylor.py`, `scripts/be_odefun.py`)
| quantity | A: order-60 Taylor, 50 digits | B: mpmath odefun 40 digits, 80-term centre series | C: DOP853 double |
|---|---|---|---|
| ξ₁ | 6.45075144417407365849871938721 | 6.450751444174073658498719387 | 6.450751444173965 |
| m(ξ₁) | 1.18222658849959972548123101927 | 1.182226588499599725481231019 | 1.182226588499598 |
| e^{−w(ξ₁)} | 14.0420320486407777628464529022 | 14.0420320486407777628464529 | 14.042032048640330 |

w(ξ₁) = −2.642055120934054732, w'(ξ₁) = −0.377398368073331047. Closed form: dm/dξ = ξ²e^{w/2}(e^w − w'²/2)/√(4π), zero iff w'² = 2e^w (v = 2u in Milne's variables).
Margins: ξ₁ ≥: 4.417e-8; ξ₁ ≤: 5.583e-8; m ≥: 8.850e-8; m ≤: 1.150e-8 (tightest); contrast ≥: 4.864e-8; contrast ≤: 9.514e-7.

## 3. Printed values (typeset = arxiv.org/pdf + pdftotext by the referee)
| source | printed | how read |
|---|---|---|
| Galli, Walmsley & Gonçalves 2002, arXiv:astro-ph/0208416 §2 eqs. (1)–(2) | M_BE ≃ 1.182; ξ_max < 6.451; stable for ρ_c/ρ_b < 13.98 | typeset text |
| McKee & Ostriker 2007, arXiv:0707.3514 eq. (15) | 1.182; R_BE 0.486; "contrast of 14.1" | typeset text |
| Larson 2003, arXiv:astro-ph/0306595 eqs. (5)–(6) | 0.48; 1.18 | typeset text |
| Burkert & Alves 2009, arXiv:0809.1457 | m_max 1.18 at ξ_max = 6.5 | typeset text |
| Krumholz notes, arXiv:1511.03457 (6.103)–(6.104) | 1.18 | typeset text |
| Bonnor 1956, Ebert 1955 | not read | — |
Galli et al.'s 13.98 disagrees with 14.042; the others are consistent roundings. No rigorous enclosure found (one search; UNVERIFIED absence). Remark: Ebert 1957 is often cited for the stability result (cosmetic).
