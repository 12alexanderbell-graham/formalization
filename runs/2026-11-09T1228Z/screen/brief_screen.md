# Brief: prior-art screen of one number (run 2026-11-09T1228Z)

Question: for the Falkner–Skan equation f''' + f f'' + β(1 − f'²) = 0, f(0) = f'(0) = 0, f'(∞) = 1, at β = −0.1 (wedge exponent m = β/(2 − β) = −1/21), the attached (Hartree, exponentially decaying, f'' > 0) solution has wall shear f''(0) ≈ 0.31926975984. Note other normalisations: f''' + ((m+1)/2) f f'' + m(1 − f'²) = 0, or f''' + f f'' + β(1 − f'²) with η scaled by √2 etc.; map each source's value to this normalisation before comparing.

1. To how many digits has this wall shear been printed, and where (author, year, table, value as printed)? Classical tables (Hartree 1937, Smith 1954, Cebeci & Keller, Asaithambi, Rosenhead…), modern high-precision papers (e.g. series/Chebyshev/shooting with many digits).
2. Has any rigorous (interval arithmetic, computer-assisted, validated numerics) enclosure of this value, or of any Falkner–Skan wall shear with β < 0, been published? Has any formal (Lean/Coq/Isabelle) one?
3. Is the classical statement that the exponentially decaying solution is unique for β* < β < 0 (Iglisch & Kemnitz 1955, Hartman 1964) stated with the class f'' > 0 or with 0 < f' < 1? (One line, from what you can read.)

Rules: use WebSearch/WebFetch. For arXiv use arxiv.org/pdf only, never ar5iv, never arxiv.org/e-print or export.arxiv.org. A failed, blocked or timed-out WebFetch/WebSearch is recorded as "not read"; never fetch the same content with curl, wget or code. Any downloaded file goes to a temp dir outside /home/claude/formalization. Do not read the repository. Write your report to `runs/2026-11-09T1228Z/screen/REPORT.md` (sources with what you actually read vs. only saw cited; every printed value with its normalisation and your conversion). Do not commit.
