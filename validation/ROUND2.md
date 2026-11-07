# Expert validation, round 2 (addendum to PROTOCOL.md, written 2026-11-07 before any expert is contacted)

Round 1 (the packet in `validation/packet/`, key `validation/sealed/KEY.json`, planted defects
`validation/controls.json`) was **never sent** and is retired: the repository is public, so its key and its
planted defects can be read by anyone, which breaks PROTOCOL.md §3 ("the repository must not be shown to
experts"). Round 1's files stay as they are (no deletions); CI keeps regenerating them as before.

Round 2 follows PROTOCOL.md (questions, sample rule, scoring, validity) with these changes:

1. **Secret planted items.** Eight fresh planted controls (one per PROTOCOL.md §3 class, none reusing a
   round-1 base headline or defect) and a random salt are kept **off GitHub**, in a sealed bundle given to
   Alexander. The draw and the positions are seeded by SHA-256(PROTOCOL.md + this file up to the commitments
   marker + salt), so nobody can compute which positions are planted from public files.
2. **Commitments.** Only SHA-256 hashes of the packet, the key, the controls and the salt are committed here.
   After all answer forms are in, Alexander returns the sealed bundle; the program checks the hashes against
   this file before opening the key, and only then commits the bundle.
3. **Generation.** `python3 validation/make_packet.py --secret <dir outside the repository>` at the commit
   named below reproduces the packet byte for byte from the bundle.
4. **Reviewers.** At least four, independent of the program, of each other and of the authors of the cited
   papers: a cosmologist, a chemical thermodynamicist, an applied mathematician (ODEs and boundary-value
   problems: the simulation, mathematics and fluid items) and a Lean 4 / Mathlib reader (Q2 on every item).
   Every item is read by its domain reviewer and the Lean reader.
5. **Reviewers are told** not to search the web for the items or the system (README_FIRST.md of the packet).
   The key is no longer public, but comparing items with the repository's records (e.g. CLAIMS.md) could still
   expose the planted changes, and those records must not be consulted before submitting; so the rule stands.
6. **Sending is recorded** in `validation/SENT2.md` (date, the commit below, reviewer codes R1–R4; no names).

<!-- commitments -->
## Commitments (SHA-256; round 2 generated 2026-11-07 from the repository state of the commit that adds this file)

- Packet (`packet/*` files sorted by name and concatenated, as printed by `make_packet.py --secret`): `4a677377995573b668572004600c0b23c1c3d1319ca4f8ff2fb14b6beea911c1`
- Answer key (`sealed/KEY.json`; also printed in the packet's MANIFEST.md): `09d76abdb6b2af16c5fd18f33bf643d526f8da3e9dbd8a5cb72cbc3ffa1c42eb`
- Planted controls (`controls.json`): `503eed760ccfc67e012817f7f755a2a29de988c02f04adcdc9bffed8dd3ebd34`
- Salt (`salt.txt`): `7609b8d1dcabaacfe2889ca02b0cf24ba3838eff11a7d2deceb09cceb1a38fe3`
- Items: 54 (46 genuine, 8 planted). Sealed bundle held by Alexander, not in this repository.
