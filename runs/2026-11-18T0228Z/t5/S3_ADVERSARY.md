# S3 (a word rule against withdrawals of registered headlines in STATE.md/README.md) — built, attacked, not shipped

Built this run (patch: `s3_not_shipped.patch`): a clause of STATE.md or README.md that names a registered headline in
backticks may not contain a withdrawal word (withdrawn, retracted, superseded, obsolete, revoked, no longer PROVED,
not PROVED, must/should/do not be cited/relied/used, cannot be cited). It caught the measured defect W′ and passed
the current STATE.md and README.md (after clause splitting; line-level matching flagged two correct lines about
superseded CI runs).

Adversary (Sonnet subagent, 10 minutes, `s3_errors` against the real registry): about 40 bypasses in six classes —
synonyms (invalid, not proven, unproved, deprecated, refuted, may not / shall not be cited, not to be relied upon,
under review, on hold), name forms (bare name, prose description, module name, double backticks, `<code>`),
clause splitting (`**Withdrawn:** N` — the control's own shape without its date —, parentheses, "e.g.", two
lines), markup (`*no longer* proved`, strikethrough, a backticked status word), Unicode (zero-width space, soft
hyphen, Cyrillic і) — and false positives on correct lines (a scope disclaimer "not proved for n > 2", a
correction of a false withdrawal note).

Decision: not shipped. It is the deny-list shape the program's own record (blind rounds F–T, LEDGER) says does
not converge, it can reject correct lines, and its control shape is bypassed by deleting the date. The class is
recorded as open in STATE (hand-written status sentences about registered headlines, in STATE.md and run
records), with the measured reader effect in `READERS.md`.
