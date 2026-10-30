# Fidelity audit (annex XL): `Checked/Fidelity/FriedmannLCDM.lean` (run 2028Z)

Promoted: `FriedmannLCDM` (definition), `isFlatLCDM_iff_friedmann`, `FlatLCDMSpec2`, `isFlatLCDM_meets_spec2`, `flatLCDMSpec2_pins`, anchors `milne_notFlatLCDM`, `coshBounce_isFlatLCDM` (proofs moved from `Work/Fidelity/SpecGapsLCDM.lean`, renamed).

| Check | Result |
|---|---|
| Frozen statement | `FriedmannLCDM` frozen in commit 3a4a5b8 (`Work/Fidelity/FriedmannBlind.lean`) before any proof about it; copied verbatim (`diff` of the def body: identical). |
| Blind restatement | The definition *is* the blind restatement: written by a subagent from the Friedmann and dust-continuity equations, told not to read any repository Lean file. The equivalence theorem closes it in Lean against the program's `IsFlatLCDM`, for every Ω, a, t₀. |
| Referee | `referee_friedmann.md`: STANDS. Every field checked; closed forms (EdS, sinh, sin, cosh bounce, de Sitter) verified with sympy. |
| Not vacuous | EdS (`einsteinDeSitter` in the blind file), and every positive anchor of `FlatLCDMSpec` via the equivalence (`friedmann_meets_spec2`). |
| Not trivial / bites | Milne `a = t` fails for every Ω (`milne_notFlatLCDM`); contracting de Sitter, wrong-Ω EdS/de Sitter, one-sided splices fail (inherited anchors). |
| Junk values | No `√`, no division by a possibly-zero quantity: `a > 0` near t₀; `DifferentiableAt` guards `deriv`; `ȧ(t₀) > 0` makes `H₀² ≠ 0` in the Ω quotient. |
| Quantifiers | `∃ ρ Λ` outside `∀ᶠ` (Λ constant, ρ a single function); `ρ` is pinned near t₀ by `ρ a³ = const`. |
| Pinning | `flatLCDMSpec2_pins : FlatLCDMSpec2 P → P = IsFlatLCDM` (on the whole domain, not only a physical subdomain). |
| Error class | None found. Residual trust: the blind writer and the program are the same model (correlated misconception possible); mitigated by the closed-form anchors written by a different subagent (run 1828Z) and the referee's sympy checks. |

Verdict: AUDITED.
