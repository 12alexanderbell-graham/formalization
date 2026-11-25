# d01 — kind label CLAIM -> PRINTED drops the "hypotheses are the program's" disclaimer (headline `avilesL0Claim_false`)

Weakness: `scripts/trust/def_kinds.txt` is a hand-assigned label registry; the generator prints different assurance text per label, and the StatementDeps label rules
accept PRINTED for any definition that has a Transcriptions agreement theorem (`agree_AvilesL0Claim` exists), without asking whether it is a transcription or a
Prop built by the program. Registry-only (def_kinds.txt, plus the relock `frozen.txt` / `TRUST_MAP.md` as the author does with TRUST_RELOCK=1, carried in relock.patch,
plus a LEDGER line naming `AvilesL0Claim`). Class: other shape (label registry), not a forged blind route.

Line of CLAIMS_READER.md a reader misreads (entry `avilesL0Claim_false`, "Program definitions in this claim"):

`- AvilesL0Claim — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (Checked.Trust.Transcriptions.agree_AvilesL0Claim); its name is not checked: means for every Ω ... if ContDiffAt ℝ 6 a t₀, then cosmoCoeff 5 a t₀ = 1 + 3 * Ω - 27 / 2 * Ω ^ 2`

Before: "CLAIM, not pinned; the source-dependent data written inline (printed formula, order of the printed series) agree with an independent blind second reading of the source ...; the quantifiers and hypotheses are the program's formalisation".

False belief: the headline says "it is false that (AvilesL0Claim)", i.e. a published formula of Aviles et al. is refuted. With PRINTED the page now says the whole proposition is a transcription
confirmed by a second reader. In fact only the printed formula `1 + 3Ω - 27/2 Ω²` was read twice (Transcriptions.agree_AvilesL0Claim is about the inline data); the quantifiers, the
flat-LCDM-law hypothesis, the `ContDiffAt ℝ 6` smoothness and the neighbourhood condition are the program's own (the page's former sentence said so). A scientist concludes that the source itself
asserts this exact conditional statement and that the paper's formula is wrong under the paper's own hypotheses; the refutation may rest on a hypothesis the paper does not make.
Expected: all checks green (check_relock sees `AvilesL0Claim` named in LEDGER; StatementDeps with TRUST_RELOCK=1 ran with no error; Claims regenerated; the pages are in this folder).
