# Run 2026-11-08T0228Z (scheduled)

**THE RESULT:** part 1 moved (rotation: four runs without part-1 progress) together with part 5: the validated simulator is now generic in the index of the Lane–Emden equation, and a second row of the classical table of polytropes — index two: first zero, mass factor, central concentration — is certified for every solution, with existence, blind closure, referee and blind literal reading, frozen, proved and promoted to Checked in one run.

**What can a scientist now trust without checking it themselves, that they could not before?** That every solution of the Lane–Emden equation of index two (θ'' + (2/ξ)θ' + θ² = 0, θ(0) = 1, regular at the centre) has its first zero in [4.3528745959, 4.3528745960], mass factor −ξ₁²θ'(ξ₁) in [2.4110460120, 2.4110460122] and central concentration in [11.402542860, 11.402542864], and that such a solution exists — checked by the Lean kernel (local build; CI pending), with every number in the statement recomputed by a blind reader.

**Measure:** Checked headlines 188 → 189 (NV witnessed); literal-reading registry +1 line (10 blind reader constants); certified rows of the polytrope table 1 → 2; generic simulator modules 3 (any integer index). CI infrastructure: one class of red runs (transient Actions-API 5xx in `ci_changes.py`) removed.

**Weakest unchecked step:** the choice of what to certify still rests on the author: the reader's rounding rules (step sizes of the windows and the range end D) were written by the author knowing the frozen windows, so the reading checks the values independently but not that the windows are the natural ones; and the classical table itself (Chandrasekhar, Horedt) was not read by the typeset route, so "agrees with the printed table" is the referee's memory, not a check.

## What we did
- Start: LOCK (06bdbe2); elan + Mathlib cache. CI read: ef070d8 (42435148596) green; heartbeat dce69bf (42433241486) red in the changes job on one HTTP 504 from the Actions API → `scripts/ci_changes.py` retries transient failures (5 attempts, then fail closed; controls: 503 raised after 5, 404 after 1) (commit after 06bdbe2).
- Rotation: part 1 four runs old. Chosen step: a published-table row by a generic simulator (STATE exact next step 2, part-1 candidate "a rigorous simulation checked against a published table of values"). Float study with the generalised generator `scripts/gen_len.py <n>`: index 2 reaches 2·10⁻¹² at the zero with the existing sup-norm cells; index 4 only ≈ 4·10⁻⁶ (sup-norm Grönwall factor ≈ e¹⁵ over [0, 15]) → index 2 now, index 4 needs weighted cells.
- Freeze d65a231 (`Work/Math/LaneEmden2.lean`). In one message: fork (generic modules `LENStart`, `LENCell`, `LENCellQ`, ≈ 3 min), blind restater (Sonnet), referee (Sonnet, STANDS).
- Certificates `emit_len.py` → `LE2Start`, `LE2QData` (64 cells, 5 kernel-decided segments), `LE2Last`, `LE2Chain`; headline proof (`core` as for index 3); axioms standard (166b676).
- Fork: existence (`LE2Exists*`, clamped flow with per-cell box conditions, since θ³/3 is unbounded below); blind closure `Work/Math/LaneEmden2BlindClosed.lean` (b297597).
- Blind literal reader: brief 924714c → reading d2d0608 (all numerals agree; 33 digits by two routes). check_blind_route B3 rejected that route (the template split the `le2Conc` header over two lines, so a ≥ 25-character code line of the reading occurred in the brief): second brief 0ba127f (one-line template) → second reading (same numerals) → copy `Checked/Trust/SecondReadingLE2.lean`.
- Promotion: `scripts/promote_le2.py` (13 modules, number-free module docs, specific imports), NV witness, registrations (headlines, literal readings, audits), full `lake build Checked`, StatementDeps with relock, Claims, packet, trust checks.

## Files
- `scripts/`: `gen_len.py`, `emit_len.py`, `gen_exists.py`, `promote_le2.py`.
- `blind/LaneEmden2Blind.lean`, `referee_le2.md`, `le2_reader/` and `le2_reader2/` (brief, reading each; the copy is from the second).
