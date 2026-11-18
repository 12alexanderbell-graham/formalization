# Run 2026-11-18T1028Z (scheduled)

**THE RESULT:** parts 2 and 5 by rotation (STATE 1l → 1j). The exact-count theorem for radial solutions of the Gelfand problem in the unit ball of ℝ³ now carries **numbers for both band ends**: `Checked.Math.GelfandPDECountValues.gelfand_pde_radial_count_values` — none above λ* ∈ [3.321992118, 3.321992119], one at λ*, two on (λ₂, λ*), one on (0, λ₁), two at λ₁, three at λ₂, with **λ₁ ∈ [1.664155, 1.664157]** and **λ₂ ∈ [2.10852, 2.10858]** (before: only 0 < λ₁ < 2 < λ₂). Frozen 6ece4ff before any proof, proved da17c09 (statement unchanged), promoted to Checked by this run's final push; referee STANDS (own 20-digit values λ₁ = 1.6641561898, λ₂ = 2.1085411021); blind restatement (encard of restrictions, all six count clauses) closed in `Work/Math/GelfandPDECountValuesBlindClosed.lean`.

**What can a scientist now trust without checking it themselves, that they could not before?** The values of the radial Gelfand branch at its first minimum and second maximum in the 3-D ball — the parameters where the number of radial solutions changes from one to three and from three to two — to six and five decimals, as part of an exact-count theorem, kernel-checked from no assumption but the equation.

**Weakest unchecked step:** the statement's fidelity rests on the same-model referee and blind restatement (both Claude); the numbers are self-certifying (the sharpness clauses pin λ₁, λ₂ as band ends, the referee's independent 40-digit integration lies inside both windows with margins 8.1e-7 and 2.1e-5).

## Start
- 10:28Z. add_repo not exposed; checkout detached at 7d5b41c = origin/main; `git checkout main`. No LOCK → taken (c1bcd8c).
- CI at start: 44261574038 (adcb9a6, a descendant of the promotion 25fd5dd of `gelfand_pde_radial_count`): goal guard, packet, changes, work, nanoda shards 0, 1, 3 green; nanoda shard 2 and the checked job running. 44275141268 (7d5b41c) pending. Not judged at start (see End).
- Local Lean: elan + `lake exe cache get` ≈ 3 min; `checked-build` of 44238855382 (543a0a0) ≈ 3 min download, restored with DELETE_ZIP=1; `lake build Checked` to this run's tree ≈ 8 min (GLamData 180 s).

## Bottleneck (and what a yes/no changes)
- The count theorem's bands were only bounded against two (λ₁ < 2 < λ₂): a reader could not use the band ends. Question: can the certified-cell machinery enclose the branch at its second and third turning points (s ≈ 37.5 and 429) and identify them with the existential turning sequence of `gelfand_extrema`? Yes → numbers for both band ends, and the method carries to Bonnor–Ebert exact counts (same equation).

## What we did
1. Exact-rational generator `scripts/gen_gl.py`: 230 homology cells (`Checked.Math.BEHCell` cells, unchanged check) from A = 4.071496844 (start box from `Checked.Math.GCerts.chain`) to 428.95, adaptive steps on the invariant margin; segments v > 2 on [4.071496845, 37.526789], u < 1 on [37.526789, 37.526809], v < 2 on [37.526809, 428.88], u > 1 on [428.88, 428.95], v > 2 at the end. Enclosure radius 3.7e-11 at the start, 2.6e-8 at ζ₁, 5.2e-6 at ζ₂.
2. Frozen statement 6ece4ff (windows from the generator: λ₁ ∈ [1.6641559157, 1.6641563188], λ₂ ∈ [2.1085207223, 2.1085788392]). Blind restatement (Sonnet) and referee (Opus) in one message: referee STANDS (`referee/REPORT.md`).
3. Lean: `GLamCell` (chains with invariants v ≷ 2, u ≷ 1 and a u-band), `GLamData`/`GLamChain` (emitted by `scripts/emit_gl.py`, 23 kernel-decided segments), `GLamBands.bands` (zeros of v − 2 by IVT; identified with the given ζ₀, ζ₁, ζ₂ by `no_both` on two points per case; λ = 2u at a zero), `GelfandPDECountValuesMain` (the count proof copied with these values). Standard axioms locally.
4. Blind statement: two compile repairs (non-Mathlib name `InnerProductSpace.laplacian` → `Δ`; the binder type of the restriction) recorded in its module doc; closed from the headline.
5. Promotion by `scripts/promote_gelfand_values.py`; NV witness; headlines, literal_readings (the parent's readings; the new decimals are certified targets, check_literals a2); StatementDeps relock, TRUST_MAP, CLAIMS, packet.

## Measure
- Band ends of the Gelfand count enclosed: 0 → 2 (widths 2e-6, 6e-5).
- Headlines 295 → 296.

## End
- (filled at the end of the run)

## Next
- STATE 1m.
