# Printed-values screen brief (run 2026-11-12T0427Z): Bonnor–Ebert constants in print

Goal: list published values of the Bonnor–Ebert critical constants, digit for digit, with the exact source and location, so that a certified enclosure can be compared with them. Do NOT read `Checked/`, `Work/`, other `runs/` folders, `*.md` files of the repository or git history. Write your result to `runs/2026-11-12T0427Z/screen/READING.md` (if Write is refused, put it in your final message).

Constants (isothermal sphere, ψ'' + (2/ξ)ψ' = e^{−ψ}, ψ(0) = ψ'(0) = 0; ρ = ρ_c e^{−ψ}): the critical dimensionless radius ξ_max (often 6.45, 6.451, 6.5), the critical centre-to-edge density contrast ρ_c/ρ_0 (often 14.0, 14.04, 14.1), and the critical mass coefficient m in M_BE = m c_s⁴ G^{−3/2} P_ext^{−1/2} (often 1.18, 1.182). Also note any value given for the dimensionless pressure or for the radius in physical form (R_BE = 0.41 G M / c_s² or similar) if printed beside these.

Rules:
- arXiv papers: download only `https://arxiv.org/pdf/<id>` (curl to a temporary directory OUTSIDE the repository, e.g. under /tmp), find the page with `pdftotext -f p -l p`, render it with `pdftoppm -r 200 -png`, crop the relevant lines with PIL and save crops (≤ 200 KB each) to `runs/2026-11-12T0427Z/screen/typeset/`; read the digits from the PNG with your Read tool. Never use ar5iv, export.arxiv.org or arxiv.org/e-print.
- Non-arXiv pages: WebFetch only; mark each such value UNVERIFIED (a summarising model sits between you and the page). Never re-fetch such a page with curl/wget/python.
- Aim for 8–15 sources: the originals (Ebert 1955, Bonnor 1956 — likely not on arXiv; report what secondary sources say they print), textbooks or lecture notes on arXiv, and widely cited star-formation papers (e.g. Alves, Lada & Lada 2001 on B68; reviews of dense-core stability). Prefer typeset arXiv readings.
- One line per value: source | location (page, equation, table) | constant | printed digits | how read (typeset crop file / WebFetch UNVERIFIED).
- Finish with a short list of values that disagree with each other in the printed digits.
