# Prior-art screen for the next part-2 target (run 2026-11-07T0028Z; Sonnet subagent, web only)

Summary of the subagent's report (its own words condensed; READ = fetched, RECALL = its memory, unverified). Two fetches were blocked (arXiv 2210.14045, arXiv 1205.1704): recorded as not read.

1. **Townes soliton** (Δ Q − Q + Q³ = 0 in R², ground state): Q(0) ≈ 2.20620, ∫Q² ≈ 11.7009 (RECALL; Chiao–Garmire–Townes 1964, Fibich 2015). No rigorous enclosure found; no formal verification found.
2. **Blasius** f''(0) ≈ 0.332057336215 (RECALL, Boyd). READ: arXiv 2008.01671 quotes 0.332057 without error bounds. No interval enclosure found (to be checked again: validated-numerics literature not searched exhaustively).
3. **Hastings–McLeod** (Painlevé II): q(0) ≈ 0.3670615515, q'(0) ≈ −0.2953721054 (RECALL; Fornberg–Weideman, Bornemann). No rigorous enclosure found.
4. **Thomas–Fermi**: OEIS A231786 (READ) lists the slope to thousands of digits from high-precision numerics (Amore–Boyd–Fernández 2012, Boyd 2013, Englert 2026); not called rigorous there. The program's enclosure agrees.
5. **Gelfand 3-D ball**: second turning point ≈ 2.1 (RECALL), no rigorous value found; no formalisation of Gidas–Ni–Nirenberg / moving planes found.
6. Suggestions: Falkner–Skan wall shear (Hiemenz 1.2325877…), separation β ≈ −0.1988.

Ranking by the screener: Townes (∫Q², Q(0)) > Hastings–McLeod > Blasius > Gelfand second fold > Thomas–Fermi.

Caveat (screener): absence from search results is not proof of absence in print. Before freezing any of these, a referee must search the computer-assisted-proof literature specifically (validated numerics journals, Lessard, Zgliczyński, Breden, van den Berg, Tucker) — the screen was thin.
