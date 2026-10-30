# Physics referee report: Fidelity specs

Scope: only the `structure … : Prop where` blocks of `LumDistSpec` (Work/Fidelity/LumDistSpec.lean),
`HubbleSpec`, `DecelSpec`, `AngDistSpec`, `FlatLCDMSpec` (Work/Fidelity/MoreSpecs.lean) and
`LumDistSpec2` (Work/Fidelity/LumDistSpec2.lean). No proofs or other files were read.

Conventions used: c = 1; metric ds² = −dt² + a²[dχ² + S_K(χ)² dΩ²]; χ = ∫_t^{t₀} ds/a;
1 + z = a(t₀)/a(t); d_M = a(t₀) S_K(χ); d_L = (1+z) d_M; d_A = d_M/(1+z) = a(t) S_K(χ).

Closed forms were derived by hand and checked with sympy. Every residual below is identically zero:
de Sitter d_L, d_A; contracting de Sitter d_A; Milne d_L, d_A; static closed d_L, d_A(R); static flat d_A;
Etherington consistency of the LumDistSpec and AngDistSpec anchors (de Sitter, Milne, static closed);
the (a, K) → (c a, c² K) invariance of a₀S_K(χ) for K > 0 and K < 0; H for tⁿ; H under time reversal; q for de Sitter, tⁿ, (−t)ⁿ and EdS;
flat-ΛCDM Friedmann identity H² = H₀²[Ω(a₀/a)³ + 1 − Ω] for t^{2/3} (Ω = 1),
sinh^{2/3} t (Ω = 1/cosh² t₀) and sin^{2/3} t (Ω = 1/cos² t₀), also checked numerically at sample points.

References marked "(mem)" are from memory and were not checked against the text in this run.

| Spec | Field | Verdict | Reference | Note |
|---|---|---|---|---|
| LumDistSpec | deSitter | CORRECT | Hogg 1999 eq. 21 (D_L=(1+z)D_M) with D_M=D_C for Ω_k=0 (mem); standard d_L=z(1+z)/H₀ for de Sitter | χ = e^{−t}−1 = z, d_L = z(1+z). The range t ≤ 0 is the past, so the hypothesis is adequate. |
| LumDistSpec | milne | CORRECT | Hogg eq. 16/21 with Ω_k=1 (mem); Milne d_L = z(1+z/2)/H₀ | χ = ln(1/t), sinh χ = (1/t − t)/2, d_L = (t⁻² − 1)/2. a = t with K = −1 solves ȧ² = −K. |
| LumDistSpec | staticClosed | CORRECT | Weinberg §1.4, d_L = a₀ r₁ (1+z) with r = S_K(χ) (mem) | a ≡ 1, K = 1, so d_L = sin(t₀ − t). Note: no bound χ < π is imposed. Beyond the antipode the textbook formula gives sin χ ≤ 0. That is what a₀S_K(χ)(1+z) literally yields. A definition using \|S_K\| would fail, but that is not the textbook formula. |
| LumDistSpec | rescale | CORRECT | Standard gauge freedom of a₀ (K/a² invariant) | Verified: c·S_{c²K}(χ/c) = S_K(χ), and z is invariant. The field is unconditional (it also constrains values on junk inputs). Natural Lean definitions still satisfy it: ∫ c⁻¹f = c⁻¹∫f unconditionally, (c x)/(c y) = x/y even when y = 0, and admissibility is preserved for c > 0. Only exotic definitions could fail it. This is a mild over-reach but harmless. |
| HubbleSpec | logDeriv | CORRECT | Weinberg §1.5; Hogg §3 H = ȧ/a (mem) | The hypotheses a(t) > 0 and differentiability at t make log∘a differentiable. This field alone pins H on the physical domain. |
| HubbleSpec | deSitter | CORRECT | Ryden ch. 5 (mem) | H = h for every h, including h ≤ 0. The function is positive and smooth everywhere, so no junk is involved. |
| HubbleSpec | powerLaw | CORRECT | Ryden ch. 5: a ∝ t^{2/(3(1+w))} (mem) | H = n/t for t > 0 and any real n (n = 0 gives a ≡ 1 and H = 0, consistent). rpow is smooth near t > 0. |
| HubbleSpec | static | CORRECT | trivial | |
| HubbleSpec | rescale | CORRECT | — | Positivity and differentiability are assumed, so the field is a consequence of logDeriv. |
| HubbleSpec | translate | CORRECT | — | Consequence of logDeriv. |
| HubbleSpec | timeReverse | CORRECT | — | ḃ(t) = −ȧ(−t), so H_b(t) = −H_a(−t). The sign is right. |
| DecelSpec | formula | CORRECT | Weinberg §1.5 q₀ = −ä a/ȧ²; Visser 2004 eq. for q (mem) | The derivatives are supplied explicitly (a' near t, a'' at t) with a(t) > 0 and ȧ ≠ 0. The hypotheses are adequate and non-vacuous. |
| DecelSpec | deSitter | CORRECT | Weinberg §1.5 (mem) | q = −h²e^{2ht}/(h²e^{2ht}) = −1 for h ≠ 0. |
| DecelSpec | powerLaw | CORRECT | standard | q = −n(n−1)/n² = (1−n)/n. Checks: EdS 1/2, radiation 1, Milne 0, accelerating for n > 1. |
| DecelSpec | eds | CORRECT | standard | Instance of powerLaw. |
| DecelSpec | crunch | CORRECT | — | a = (−t)ⁿ with t < 0 gives ȧ = −n(−t)^{n−1}, ä = n(n−1)(−t)^{n−2}, so q = (1−n)/n. q is even under time reversal. |
| DecelSpec | rescale | CORRECT | — | The only hypothesis is deriv a t ≠ 0 (no positivity, no C²), so the field constrains junk-region values. It holds for natural definitions: deriv(c·f) = c·deriv f unconditionally over a field, and junk ä = 0 gives q = 0 on both sides. It also holds for the −1 − Ḣ/H² form with H = ȧ/a. Only contrived definitions could fail. |
| DecelSpec | translate | CORRECT | — | deriv of a translated function is unconditional in Mathlib, so the same remark as rescale applies. |
| DecelSpec | timeReverse | CORRECT | — | deriv(f∘neg) = −(deriv f)∘neg unconditionally, so ä is even and ȧ² is even. The sign is right (no minus, unlike H). |
| AngDistSpec | flat | CORRECT | Hogg eq. 18 D_A = D_M/(1+z); Weinberg §1.4 d_A = a(t₁) r₁ (mem) | d_A = a(t)χ. A positive, continuous a on [t, t₀] makes 1/a integrable. Adequate. |
| AngDistSpec | closed | CORRECT | same | a(t) sin χ for K = 1. |
| AngDistSpec | open | CORRECT | same | a(t) sinh χ for K = −1. |
| AngDistSpec | rescale | CORRECT | — | c a(t)·S_{c²K}(χ/c) = a(t) S_K(χ). Together with closed/open it pins d_A for every K ≠ 0 (scale a by 1/√\|K\|). The field is unconditional; the same harmless junk remark as LumDistSpec.rescale applies. |
| AngDistSpec | translate | CORRECT | — | The field is unconditional. It holds for natural definitions (interval-integral substitution s ↦ s + τ is unconditional in Mathlib). |
| AngDistSpec | deSitter | CORRECT | standard: d_A = z/((1+z)H₀) for de Sitter | e^t(e^{−t} − 1) = 1 − e^t. |
| AngDistSpec | deSitterContracting | CORRECT | — | χ = 1 − e^t and a = e^{−t}, so d_A = e^{−t} − 1. Here 1 + z = e^t ≤ 1, a blueshift. |
| AngDistSpec | milne | CORRECT | Milne d_A = z(1+z/2)/(1+z)² (mem) | t·sinh(ln(1/t)) = (1 − t²)/2. |
| AngDistSpec | staticClosed | CORRECT | — | χ = (t₀ − t)/R, so d_A = R sin(χ) is right for curvature radius R. It is consistent with LumDistSpec.staticClosed through rescale (K = R², a = R gives sin(t₀ − t)). The remark about no antipodal bound applies here too. |
| AngDistSpec | staticFlat | CORRECT | — | Euclidean. Also follows from flat. |
| FlatLCDMSpec | eds | CORRECT | Hogg eq. 14 E(z) with Ω_M = 1 (mem) | H = 2/(3t) and H² = H₀²(a₀/a)³ on a neighbourhood. |
| FlatLCDMSpec | deSitter | CORRECT | Hogg eq. 14 with Ω_Λ = 1 (mem) | H = h > 0, Ω = 0. |
| FlatLCDMSpec | lcdm | CORRECT | Standard flat matter+Λ solution a ∝ sinh^{2/3}((3/2)H₀√Ω_Λ t) (mem) | Verified exactly: H₀²Ω = (4/9)/sinh²t₀ and H₀²(1−Ω) = 4/9. Docstring nit: "(3/2)√Λ t" is right only if Λ denotes H_∞² = Λ_Einstein/3. With Einstein's Λ it reads (3/2)√(Λ/3) t. This is a docstring-only issue; the Lean statement is unaffected. |
| FlatLCDMSpec | negLambda | CORRECT | Standard matter + negative-Λ solution (mem) | Verified exactly: H₀²(1−Ω) = −4/9 < 0, so Ω > 1. Restricting to the expanding phase t₀ < π/2 is consistent with `expanding`. Calling a negative-Λ model "ΛCDM" is a naming choice, not an error. |
| FlatLCDMSpec | rescale | CORRECT | — | H and z are invariant under a ↦ c a. |
| FlatLCDMSpec | translate | CORRECT | — | One direction only, but the converse follows by translating back. |
| FlatLCDMSpec | expanding | CORRECT (convention) | Hogg: H₀ > 0 (mem) | Encodes the signed convention H = H₀E(z) with H₀ > 0, not H² = H₀²E². This is consistent with `contracting` and with how ΛCDM is used. It forces the predicate to include differentiability at t₀; otherwise junk deriv = 0 would violate the field, which is the desired effect. |
| FlatLCDMSpec | contracting | CORRECT (convention) | — | e^{−ht} satisfies the squared Friedmann equation with Ω = 0 but has H₀ < 0. Excluding it is the H₀ > 0 convention above. A definition stated as H² = H₀²E² would fail this field, so the field is deliberate and documented. |
| FlatLCDMSpec | edsOnlyOne | CORRECT | — | Equality on a neighbourhood forces Ω(t₀²/t² − 1) = (t₀²/t² − 1), so Ω = 1. The pointwise condition at t₀ alone is vacuous, as the docstring says. |
| FlatLCDMSpec | deSitterOnlyZero | CORRECT | — | Ω(e^{3h(t₀−t)} − 1) = 0 on a neighbourhood, so Ω = 0. |
| FlatLCDMSpec | notPastOnly | UNCLEAR (convention) | — | The piecewise a is C¹ at 0 with H₀ = 1. For t > 0, H = 1/(1+t) ≠ 1, so it is not ΛCDM on a two-sided neighbourhood. Correct under the dynamical, two-sided definition the docstring adopts. But an observational definition that imposes H(z) = H₀E(z) only for z ≥ 0 (the past light cone, as in Hogg's E(z) usage) would accept this function and fail the field. Physically the two-sided reading is defensible, since Friedmann is a time-local dynamical law. This is a modelling choice, not wrong physics. |
| FlatLCDMSpec | notFutureOnly | CORRECT | — | The past branch 1 + t has H = 1/(1+t) ≠ H₀ = 1, so the function is rejected under both the two-sided and the past-only readings. |
| LumDistSpec2 | base | CORRECT | — | Inherits LumDistSpec (all fields CORRECT). |
| LumDistSpec2 | etherington | CORRECT | Etherington 1933 reciprocity, d_L = (1+z)² d_A (mem); Hogg eqs. 18, 21 (mem) | The ∃DA is non-vacuous because AngDistSpec pins DA on every admissible (K, a, t₀, t): K ∈ {0, ±1} directly, other K through rescale. Through the redshift factor this pins D. The field is restricted to the admissible domain, so it imposes no junk requirement. Its anchors are consistent with LumDistSpec's (de Sitter, Milne and static closed all agree, checked symbolically). Assumption: `1 + redshift a t₀ t` = a(t₀)/a(t), from the `Checked.Cosmography.redshift` definition, which was not read per the instructions. If redshift is defined as a(t)/a(t₀) − 1 instead, this field would be wrongly signed. |

## Remarks on adequacy
- LumDistSpec by itself is only an anchor set: three model points plus rescale. It does not pin d_L for general a. LumDistSpec2 (through Etherington + AngDistSpec) closes that gap.
- None of the fields requires junk behaviour, such as a value at x/0, at √(negative) or at a non-differentiable point, that would contradict the physics. The unconditional invariance fields (LumDistSpec.rescale, AngDistSpec.rescale/translate, DecelSpec.rescale/translate/timeReverse with only ȧ ≠ 0) do constrain junk-region values. Natural definitions satisfy them because the relevant Mathlib identities (scalar pull-out of integrals and derivatives, translation and negation of deriv and interval integrals) are unconditional.
- No field is wrongly signed. The time-reversal signs are H odd and q even, both correct.

**Final verdict: no field states wrong physics. All fields are CORRECT except one UNCLEAR, FlatLCDMSpec.notPastOnly. It is correct under the two-sided (dynamical) definition of flat ΛCDM, but it would reject a past-light-cone-only definition. There is one docstring-only nit (FlatLCDMSpec.lcdm: "(3/2)√Λ" presumes Λ ≡ Λ_Einstein/3). LumDistSpec2.etherington is correct provided `redshift a t₀ t` = a(t₀)/a(t) − 1, which was not inspected.**
