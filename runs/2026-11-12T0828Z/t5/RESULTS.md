# Blind red team AH — necessity witness layer (run 2026-11-12T0828Z): results

Red team: Sonnet, blind, brief `briefAH.md` (committed first, 2feecc4), snapshot f41efd8 read-only, output verbatim in
`redteamAH/` (committed before judging). Judge tree `../fzJ` at f41efd8 with the CI build restored from artifact
`checked-build` (run 43155541876; restore 72 s, `lake build Checked` on top 1.5 min). All six defects compiled.

## BEFORE (checks of main f41efd8; author relocks and regenerates; `local_frozen_step.py --trust f41efd8`, then every
python check of the trust step run individually so that a failing early check does not hide later ones)

| d | weakness | valid? | caught by | the necessity layer (StatementDeps + check_necessity --base) |
|---|---|---|---|---|
| d01 | wrapper conjunct `redshift a t₀ t₀ = 0` makes `a t₀ ≠ 0` NEEDED | **INVALID**: the generated line ("needed 3") is true of the wrapper statement, in Lean and on paper (z(t₀) is undefined when a(t₀) = 0) | check_literals rule 1; V1/V13 | accepted (line true) |
| d02 | duplicate headline double-counts witnesses (tally 54/154 → 55/155) | valid | **check_claim_vocab D1** (identical generated claim); also literals, V13 | accepted |
| d03 | `H : ℝˣ` hides `deriv a t₀ ≠ 0` | valid | check_literals rule 1, V1/V13 only (incidental: a literal-free headline and disclosed vocabulary avoid both) | **accepted**, counted fully classified |
| d04 | `PLift (0 < 1 + u + w)` as data, never numbered | valid | check_literals rule 1, V1/V13 only (incidental) | **accepted**, counted fully classified |
| d05 | `p ∈ {q \| -2 < q.1 ∧ 0 < 1 + q.1 + q.2}`: two conditions as one part | valid | check_literals rule 1, V1/V12/V13 only (incidental) | **accepted**, counted fully classified |
| d06 | one redundant hypothesis next to one redundant part, no "each alone, not together" label | valid (and **present on main** in 7 headlines: `Aviles.flatLCDM_coeffs`, `CPL.flatCPL_coeffs`, `CPL.printedL0_ne`, `Records.F1_l0`, `F2_toy`, `F2_error`, `F3_D4_LCDM`) | StatementDeps "hypotheses are conjunctions" (the planted copy only) | accepted (label rule) |

Full CI: 0 of 5 valid defects accepted. The layer under test (shape detection + `check_necessity.py --base`): 4 of 5
valid accepted (d02–d05; d02's duplicate is D1's job and D1 catches it); d06's planted copy was stopped by the
conjunction-hypothesis rule, but its label hole was live on main. The full-CI catches of d03–d05 are incidental (literals in the copied statement, words of the
author's paraphrase): a genuine headline without numeric literals and with disclosed vocabulary passes both.

## Repairs (written after reading the report — not blind), commit 6c02253

- `scripts/trust/StatementDeps.lean` `carriesProof`: a binder whose type (after `∀`s, at default transparency) is a
  subtype or an inductive type with a proposition field in some constructor (`ℝˣ`, `PLift P`, `Fin n`), or has such a
  type among its type arguments, gets the shape reason `subtype` (d03, d04).
- `Checked/Trust/NonVacuity.lean` `partsWalk`: a `Membership.mem` atom is unfolded at default transparency and walked
  when it is a conjunction, `∃`, `∃!`, `↔` or `∀` (d05: `bundled 1`); obligations and the shape detector use the same
  walk (rule of run 2026-11-11T1628Z).
- `StatementDeps` label: "each alone, not together" when the redundant hypotheses and redundant parts of a headline
  number two or more together (d06); the seven headlines above are relabelled.

## AFTER (same judge tree, defects d01–d05 applied, repairs on top)

`check_necessity --base f41efd8`: FAILED, N4 on exactly `LookbackUnit.lookback_second_order_unit` (`subtype`, d03),
`Chemistry.CubicEOSLift.critCubic_existsUnique_lift` (`subtype`, d04), `Chemistry.CubicEOSRegion.critCubic_existsUnique_region`
(`bundled 1`, d05). No existing headline gained a shape reason; every existing witness still compiles (rebuild 2.5 min);
fully classified 59 → 56 of 159 on the judge tree (the three defects). Layer acceptance after: d03–d05 rejected (N4),
the d06 label hole closed; d02 still passes the necessity checks and stays D1's catch.

## Open
- A part-level witness never shows joint redundancy; the label is a caveat, not a check (AF d02, unchanged).
- `carriesProof` looks one constructor deep and through type arguments (fuel 4); a proof hidden in a field of a field's
  type (a structure whose field is a structure with a Prop field) is not reached. Next round: aim there.
