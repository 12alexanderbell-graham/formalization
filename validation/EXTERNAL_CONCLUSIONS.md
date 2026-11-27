# External test: conclusions and next phase

Run 2026-11-26T1529Z, written after the last verdict (PROMPT, Alexander 2026-11-26 ~22:10Z: "stop, conclude,
then plan"). Detailed records: `EXTERNAL_S.md`, `EXTERNAL_T0.md`, `EXTERNAL_T1_T2_T3.md`, `EXTERNAL_BLOCKERS.md`.

## 1. Per target

| target | verdict | caught | missed / not reached | time |
|---|---|---|---|---|
| S1 Erdős 304 (OpenAI) | DONE | frozen statement ⟺ blind reading plus existence of expansions (without it `sInf` gives a junk 0); a list-monad elaboration in `IsExpansion` (harmless) | no human review of this family exists to compare with | statements 30 min for S1–S3 together; replays 50 min local, then GitHub |
| S2 Erdős 184 (OpenAI) | DONE | ⟺ blind reading (transport to every finite vertex type) | the human thread could not be fetched (robots.txt, not worked around) | as above |
| S3 van der Waerden (OpenAI) | DONE | the frozen statement does not give finiteness of W_r(k) for small k; proved here from Hales–Jewett so no `sInf` is junk | the erdosproblems.com entry was not found; the manuscript's citation of Erdős was used | as above |
| family 159, Erdős 3 (OpenAI) | headline UNCOVERED | the headline bound is not formalized — the same as the human survey found | the auditor had read the survey first: shows the gate can see the gap, not that it found it unprompted | 20 min |
| T0 null-cone gravity (Chandrasekaran / GPT-6 Astra) | NOT DONE | (a) Eqs. (4.33)–(4.34) hold as printed, but for one polarization and one angular harmonic; summed over harmonics with the paper's own normalization the amplitude diverges (Lean); the phase is not needed for finiteness; (b) arithmetic equals Sen's J-summed coefficient; a candidate inconsistency was withdrawn by a referee | (b) heat-kernel coefficient and (c) Einstein operator on a space of solutions have no formal counterpart; unitarity of the paper's evolutions not formalized | (a) 40 min, (b)(c) 15 min; angular sum one further run |
| T1 Navier–Stokes (OpenAI) | DONE | frozen (C), (D) ⟹ blind reading of Clay's (C), (D); zero solution satisfies the frozen notions (no vacuous "no solution"); 610-module proof replayed, declarations identical, standard axioms, two kernels | that the Lean proof follows the written argument is not checked (not claimed) | statements 22 min; replay 6.5 h of wall time, almost all of it our own tool failures (below) |
| T2 zeta zeros, 67.2% (Alpöge–Furman / Claude) | DONE for 67.2% and Theorems 1–2; the (0,T) rate NOT DONE | the literal "67.2%" certified as a decimal; the paper's rate O(log log T/log T) is not in any Lean statement (the human audits did not report this) | our scanner raised a false `axiom` alarm (nested comments), caught only by comparing with the authors' own audit | statements 16 min; replay about 1.5 h |
| T3 AlphaEvolve rank-48 ⟨4,4,4⟩ | DONE | all 4096 tensor entries checked by the kernel; algorithm theorem over ℂ | no human review read | 14 min |

## 2. What DONE guarantees, and what it does not

A DONE means: the Lean statement the authors froze was checked by Lean to imply (or equal) a statement that a
separate reader wrote from the English claim without seeing the authors' Lean; the definitions it uses give the
right answer on small cases worked out by hand; and the authors' proof of that frozen statement was rebuilt in
their own Lean and Mathlib versions, found to prove exactly the frozen statement (every declaration it relies on
identical), uses only Lean's three standard axioms, and was re-checked by two independent proof checkers (Lean's
own kernel replay and nanoda, a separate checker written in Rust). It does not mean the claim is the right
reading of the English: that rests on one reader (one Sonnet model per claim), and turning English into Lean is
a judgment. It does not mean the Lean proof follows the paper's argument, only that the stated theorem is
proved. It trusts Lean, Mathlib and the two checkers themselves (two of the three pins are release candidates).
And it covers only what the reader wrote: a restriction the paper makes quietly (one harmonic in T0) or a remark
nobody formalized (T2's rate) is reported as NOT DONE, not certified.

## 3. Our own tool failures today, and whether any could have produced a false DONE

| failure | effect | could it give a false DONE? |
|---|---|---|
| Match step copied the challenge into `namespace Chal`; copied `structure`s became new types (T1) | false FAIL | not in this form (a kernel proof was still required), but the copy is not what the authors froze; replaced by `compare_decls.lean` |
| `compare_decls` flagged 9 unreferenced private notation declarations as MISSING (T1) | false FAIL | no; fixed to compare everything reachable from the targets — the risk moves to the reachability computation, which has one negative control so far |
| `#print axioms` output wrapped over lines not parsed (T2) | false FAIL | **yes in the other direction**: a parser reading only the first line could miss a non-standard axiom further down. Fixed; red-team item below |
| blind readings (`Readings.*`) skipped by the axiom check by module-name prefix | none yet | **yes**: a closure placed under a `Readings.` name with a `sorry` would pass the axiom check. Red-team item below |
| scanner: comment stripping without nesting → false `axiom` alarm (T2) | false alarm (advisory) | no (advisory only) |
| `sorry` in a docstring, theorems with arguments, root-level challenges, Batteries as "outside", forced `autoImplicit` | false FAIL | no |
| leanchecker over a whole closure OOM-killed (sandbox); a runner lost in batches of 20 (T1, no log) | no verdict | no; now parallel batches, each process first for the OOM killer, a failed batch re-run singly, and sharding over jobs |
| this run cancelled a healthy T1 job on a wrong time estimate | one hour lost | no |
| coverage gate written after reading a human survey (family 159) | — | it can only produce NOT DONE; but it is textual (theorem names), so a closure that cites a reading theorem without proving its statement would count as covered: hand-checked here, not by the tool |
| nanoda reports "1 pretty printer error: Unable to print axioms" (seen on S1 and T1) | none | not understood; the type checker and the axiom whitelist (hard error) are separate from the printer, but this has not been verified |

## 4. What the trust system still lacks, ranked by how much each gap weakens a DONE

1. **One reader per judgment link.** Every DONE rests on one model's reading of the English. A second and third
   independent reader (different prompts, ideally different model families) with recorded disagreements would
   turn the weakest link into a measured one.
2. **No adversarial test of the replay tool.** Each check has at most one negative control; two holes are known
   above. A DONE is only as good as the tool's ability to say FAIL.
3. **The closure and its coverage are audited by the agent that wrote them.** The coverage gate matches names,
   not statements.
4. **Scope restrictions are found by reading, not by the tool** (T0's one harmonic was caught by the reader's
   list of dependencies, not by any gate).
5. **Comparison with human reviews is thin and once not blind** (most families have no accessible human review).
6. **Infrastructure**: a 444-module closure (S4) has not finished building on GitHub; nanoda's printer error is
   unexplained; release-candidate toolchains are trusted as they are.

## 5. Next phase, ranked

1. **Red team against `replay.sh`** (no decision needed; started now). In a copy of the smallest outside closure
   (S1, Erdős 304), plant one defect at a time and require a FAIL for each: a weakened definition in the
   solution (`2 ≤ n` → `1 ≤ n`), a hidden `sorry` in a dependency, an extra `axiom` used by the proof, a renamed
   definition, `native_decide` / `implemented_by`, a non-standard axiom late in a long wrapped list, and a closure
   with `sorry` named `Readings.*`. Each must fail at the step meant to catch it; a pass is a hole, fixed generally
   and re-run on all seven.
2. **Two or more independent blind readers on every judgment link** of S1–S3, T1, T2, T3 and T0(a), each closed
   against the same frozen statement; disagreements recorded and adjudicated by a referee who sees only the
   English and the readings.
3. **`plumb`: the external test as one command** — `scripts/external/plumb <git url> <rev> <solution module>
   <challenge module> <theorems>` writes the manifest line, runs the replay locally or dispatches it, and writes
   a verdict stub listing every link; the brief → reading → closure protocol as its documented second half.
4. **Statement-level coverage instead of name-level**: the coverage gate checks, in Lean, that each closure
   theorem's type is the reading theorem's type (`type_of%` equality), not that a name appears.
5. **The remaining Erdős families of target S**, smallest closure first, with the build cache across jobs for the
   large ones (S4 cycle–clique running).
6. **Explain nanoda's "Unable to print axioms"** with a planted non-standard axiom (part of item 1).

Decision asked of Alexander: which of items 2–5 comes next after the red team.

## 6. Item 1 done (red team), 2026-11-27 ~01:45Z

`EXTERNAL_REDTEAM.md`: ten planted defects in a copy of S1's closure (weakened statement, hidden `sorry`,
extra axiom, renamed definition, `native_decide`, wrapped axiom lists with the bad axiom on either line, a
`sorry` reached through a reading, a sorry'd "closure" under a `Readings.*` name): all caught at the intended
step; nanoda rejects a planted axiom by itself. The two suspected holes of section 3: the wrapped-list parser
holds (P7b); the `Readings.*` skip cannot give a false DONE (coverage counts only `Closure.*`), but the replay's
last line said PASSED — fixed: it now states the readings' coverage (`COMPLETE` needed for a DONE).
Waiting for Alexander's choice among items 2–5.
Also: leanchecker sharded over four GitHub jobs works (run 45924592732, after the first try lost one shard's runner).
