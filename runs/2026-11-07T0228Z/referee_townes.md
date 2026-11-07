# Referee report: `Work/Townes/TownesShooting.lean` (`townes_under`, `townes_over`)

Run 2026-11-07T0228Z. Referee judged the frozen statement only. I did not open TCerts*, TChain* or runs/.../scripts/.

## VERDICT: STANDS

Both statements are faithful and not vacuous. Their hypotheses determine a unique solution, and their conclusions are mutually exclusive events of that solution. Independent float and multiprecision integration confirm that 2.2062008646 undershoots (at r ≈ 13.5210) and 2.2062008647 overshoots (at r ≈ 13.4988), both before 68/5 = 13.6. Swapping the two decimals makes both statements false. I found no published rigorous enclosure of Q(0) or of ‖Q‖₂², and no formal verification of either.

Minor remarks (no change required):
- (a) `hφ0` is redundant: it follows from `hθ` + `hφ`. It is harmless.
- (b) The radius 68/5 is tight. The margins are about 0.08 (under) and 0.10 (over). Replacing 68/5 by 13.5 would make `townes_under` false.

## 1. Attack on the statement (annex XL fidelity)

**Elaboration.** I copied `townes_under` verbatim into a scratch file and ran `lake env lean`. It elaborates with `pp.numericTypes`. The right-hand side parses as `((-((1/r) * φ r)) + θ r) - (θ r)^3`, which I checked by `rfl`. This is φ' = −φ/r + θ − θ³, i.e. θ'' + θ'/r − θ + θ³ = 0. Correct.

**Decimals.** `norm_num` proves `(2.2062008646 : ℝ) = 22062008646/10^10` and `(2.2062008647 : ℝ) = 22062008647/10^10` in the scratch file. So OfScientific in ℝ is exact. `68/5 = 13.6` exactly.

**Junk values.** `1/r` occurs only under `r ∈ Ioc 0 S`, so r = 0 is excluded. At r = 0 the only requirements are θ(0) = c, the right derivative of θ at 0 equal to φ(0), and continuity of φ within [0, S] at 0. None of these involves 1/0. All derivatives are `HasDerivWithinAt … (Icc 0 S)`, which is one-sided at 0 and at S. Values of θ, φ outside [0, S] are unconstrained and never used. No junk.

**The hypotheses determine the solution (uniqueness).**
- φ is continuous on (0, S] because it is differentiable there, and at 0 by `hφ0`.
- On (0, S], (rφ)' = r(θ − θ³). For 0 < a < r this gives rφ(r) − aφ(a) = ∫ₐʳ s f(θ(s)) ds. Since aφ(a) → 0·φ(0) = 0, we get rφ(r) = ∫₀ʳ s f(θ) ds. Hence |φ(r)| ≤ (r/2)·max|f(θ)| and φ(0) = 0 is forced.
- Then θ(r) = θ₀ + ∫₀ʳ t⁻¹ ∫₀ᵗ s f(θ(s)) ds dt. The kernel has norm ≤ r²/4 times the Lipschitz constant of f on a bound for θ. Picard/Gronwall therefore gives uniqueness on [0, S].
- `hφ0` is not needed. If aφ(a) → L ≠ 0 then θ ~ L log r, which contradicts continuity of θ at 0. So L = 0 and φ → 0 automatically. Keeping `hφ0` makes the hypotheses neither stronger nor wrong.

**The hypotheses are satisfiable (non-vacuous).**
- Local existence at the regular singular point holds by contraction for the same integral equation.
- Global existence on every [0, S] follows from the Lyapunov function E = φ²/2 − θ²/2 + θ⁴/4. It satisfies E' = −φ²/r ≤ 0, and its potential is coercive.
- So for every S ≥ 68/5 there is exactly one admissible restriction (θ, φ)|[0,S]. Each theorem is a statement about that unique trajectory.

**Quantifiers.** The statements quantify ∀ S ≥ 68/5, ∀ θ φ satisfying the hypotheses, ∃ r ∈ (0, 68/5]. This is correct, and since S ≥ 68/5 the event radius lies inside the domain of the hypotheses.

**Strength of the conclusions and mutual exclusivity.**
- Undershoot: φ(r) > 0 and θ > 0 on [0, r].
- Overshoot: θ(r) < 0 and φ < 0 on (0, r]. `Ioc` is correct here because φ(0) = 0.
- For a single (θ, φ) the two events cannot both hold. Take r₁ for the undershoot and r₂ for the overshoot. If r₁ ≤ r₂ then φ(r₁) < 0, a contradiction. If r₁ > r₂ then θ(r₂) > 0, a contradiction.
- I proved this in Lean in the scratch file (`excl`, axioms: propext, Classical.choice, Quot.sound; no sorry).
- Neither event is trivial near r = 0. There φ(r) ≈ (r/2)(θ₀ − θ₀³) < 0 and θ ≈ θ₀ > 0.
- The conclusions are the standard open shooting events, which is what the shooting/assembly argument needs. The statement does not assert existence of Q between the two values; the docstring says so honestly.

**Near misses.**
- Swapping the decimals makes both theorems false. By uniqueness, 2.2062008647 has exactly one trajectory, which overshoots (numerics below). By mutual exclusivity it then cannot undershoot. The same argument applies to 2.2062008646.
- Shrinking the radius to 13.5 would falsify `townes_under`, whose event is at about 13.521.

## 2. Independent numerics

**Method 1: mpmath Taylor integrator** (scratchpad `townes_mp.py`, `shoot_bis.py`).
- Series start at r = 0 using a_{k+2} = (a_k − c_k)/(k+2)², where c_k are the Taylor coefficients of θ³.
- Away from 0, a Taylor recurrence derived from r θ'' + θ' = r(θ − θ³).
- Event roots found by bisection on the local polynomial.

Two independent settings:

| Setting | dps | h | Order N | Q(0) bracket |
|---|---|---|---|---|
| Run 1 (24 bisections) | 40 | 0.05 | 30 | [2.2062008646507460713, 2.2062008646507460773] |
| Run 2 (20 bisections) | 50 | 0.04 | 38 | [2.2062008646507460594, 2.2062008646507461548] |

**Q(0) ≈ 2.20620086465074607** (16 significant digits agree; float, not rigorous).

The bracket edges sit 5.07e-11 above 2.2062008646 and 4.93e-11 below 2.2062008647, so both values are about 5e-11 from Q(0).

Classification:

| θ(0) | Event | Radius (mpmath, both settings agree to 12 digits) |
|---|---|---|
| 2.2062008646 | UNDER, φ turns positive with θ > 0 | r = 13.521011147769 |
| 2.2062008647 | OVER, θ crosses 0 with φ < 0 | r = 13.4988449065259 |

**Method 2: scipy float64 (`float_check.py`).** Series start at r = 10⁻³; terminal events θ = 0 (decreasing) and φ = 0 (increasing).

| Integrator | 2.2062008646 | 2.2062008647 |
|---|---|---|
| DOP853, rtol 1e-13 | under at 13.5213 | over at 13.4985 |
| Radau | under at 13.5360 | over at 13.4839 |
| LSODA | under at 13.5147 | over at 13.5024 |

All methods agree on the classification, and every event lies before 13.6. The float radii scatter in the 2nd–3rd decimal because perturbations grow like e^r near the saddle θ = 0.

## 3. Prior art

**(a) Rigorous / computer-assisted enclosures.**

READ (via WebFetch of arxiv.org/pdf or abs, or the cited abstract PDFs); none treats the Townes ground state:
- arXiv 2211.16445, "Constructive proofs for localized radial solutions of semilinear elliptic systems on R^d" (author names not shown in the fetched text; recalled as van den Berg, Hénot, Lessard).
  - Treats cubic Klein–Gordon on R³, Swift–Hohenberg on R², and a FitzHugh–Nagumo system on R².
  - Gives C⁰ error bounds only. No Q(0) and no 2D cubic NLS ground state.
- arXiv 2101.08356, "Uniqueness of excited states to −Δu+u−u³=0 in three dimensions" (recalled authors: Cohen, Li, Schlag).
  - It is 3D and uses interval arithmetic.
  - The ground-state "BOUND STATE GOOD" interval is b ∈ [4.266, 4.433]; b₀ ≈ 4.3373 is given as a float only.
  - Nothing in 2D. Other dimensions are deferred to future work.
- arXiv 2404.04054, Breden–Chu, "Constructive proofs for some semilinear PDEs on H²(e^{|x|²/4}, R^d)".
  - Treats self-similar profiles, including 2D critical NLS in the self-similar variables.
  - Gives H²(µ) enclosures. This is not the Townes soliton and gives no Q(0).
- arXiv 2503.04701, Ayala–García-Azpeitia–Lessard, gap solitons: 1D Gross–Pitaevskii with a periodic potential. Not relevant.
- arXiv 2302.12877 (abstract): a Fourier/Newton–Kantorovich method on R^m, applied to the Kawahara equation. Not relevant.
- arXiv 2603.10338: analytic uniqueness for d ≥ 3 with an inverse-square potential. No numerics.
- Cadiot seminar abstracts (KIT 2026-01-28; CANUM 2026): localized solutions on R^n, applied to Swift–Hohenberg, Gray–Scott and Whitham. No Townes soliton.
- Cwiszewski–Klinikowski–Lessard abstract (ETAMM 2026): radial solutions of a cubic equation with Coulomb/Hardy potentials on R³, using Taylor + Chebyshev + stable manifold. No Townes soliton.

Searches with no relevant hit:
- "Townes" "computer-assisted";
- "2.20620086" Townes;
- "11.7008965"/"1.86225" Townes;
- the Breden/Lessard/Plum/Wilczak/Zgliczyński radial ground-state combinations;
- an extended search on computer-assisted uniqueness of the 2D ground state.

RECALLED (not verified this session):
- Kwong 1989 (uniqueness of the positive radial solution).
- Weinstein 1983: sharp Gagliardo–Nirenberg constant and N_c = ‖Q‖₂² ≈ 11.70, i.e. 2π·1.8622.
- Fibich's monograph (2015): float values Q(0) ≈ 2.206.
- I recall no paper giving an interval enclosure of the 2D Townes Q(0) or of N_c.

**(b) Formal verification.** A search for Lean/Coq/Isabelle with NLS, ground state or Townes found nothing relevant. The hits were unrelated Lean formalizations (control theory, quantum Stein's lemma, Vlasov mean-field). I am not aware (recall) of any proof-assistant result about the Townes soliton.

## 4. Is the qualitative answer already published?

Not as far as I could find. No rigorous enclosure of Q(0), with ≥ 10 digits or any digits, was found in what I READ. Nor do I RECALL one.

The value Q(0) ≈ 2.2062008646507… is folklore from float shooting. The interval-arithmetic machinery that would produce it exists and is published for neighbouring problems (2211.16445, 2101.08356 in 3D, 2404.04054 for self-similar profiles). A rigorous 2D Townes enclosure of width 1e-10, and a fortiori a Lean-checked one, would therefore be new as far as this screen can tell. The screen is limited by the search engine and the fetched texts only.
