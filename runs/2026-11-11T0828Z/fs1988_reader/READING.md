# Reading: wall shear f''(0) at beta = -0.1988

Source read: A. Asaithambi, "On Solving the Nonlinear Falkner-Skan Boundary-Value Problem: A Review", Fluids 6(4), 153 (2021), MDPI. The title differs from the one the brief guessed; it is a review.
Equation form: f''' + f f'' + beta(1 - f'^2) = 0, f(0) = f'(0) = 0, f' -> 1 (Eq. 5-6). This is the same as the brief. Eq. 7 is a generalized form with a coefficient beta0 on f f''. Table 2 uses beta0 = 1.

Access: the MDPI PDF returned HTTP 403, so it is **not read**. I read only the HTML page (https://www.mdpi.com/2311-5521/6/4/153/htm) through WebFetch. WebFetch returns a small model's rendering of the page, not raw text. No typeset page was seen. The digits below were therefore not checked against the typeset page.

## Values (one line each)

Format: paper | table | beta | branch | printed value | attributed source | typeset seen

- Asaithambi 2021 (Fluids 6, 153) | Table 2 | -0.1988 | not stated (presumably attached/normal; the table does not label branches) | 0.005225 | Asaithambi [22] | no (HTML only)
- Asaithambi 2021 | Table 2 | -0.1988 | not stated | 0.005222 | Zhang et al. [50] | no (HTML only)
- Asaithambi 2021 | Table 2 | -0.1988 | not stated | 0.005226 | Salama [48] | no (HTML only)

Table 2 caption: "Falkner-Skan solutions (f''(0)) for selected values of beta in [-0.1988, 2]."
Text: "most works [22,48,50] have reported results for both positive and negative values of beta in the interval [-0.1988, 2]. These results are summarized in Table 2."
Neighbouring rows, for context only: beta = -0.18 gives 0.128637 / 0.128636 / 0.128638, and beta = -0.15 gives 0.216361 / 0.216362 / 0.216362, in the same column order.

Reversed-flow branch: no value at beta = -0.1988 found. The text only says Stewartson [10] first obtained reverse flows for beta in (-0.1988, 0). It also says Hartree [43] gave the physically relevant range as -0.198838 <= beta <= 4/3. No f''(0) value is attached to either statement.

## Uncertain
- The tabulated values come from the HTML as rendered by WebFetch's summarizer. I asked twice, and the second time for a verbatim quote; both gave the same digits. A transcription slip is still possible, so check them against the typeset PDF.
- The first WebFetch pass (characters 0-100000) and the second (100000-200000) found no table. The Table 2 data appeared only in the last segment (200000 onward).
- The table does not say which branch the values are, or whether the original papers used the same equation form. References [22], [48] and [50] are in the paper's reference list, which I did not read. I assume they are Asaithambi, Salama and Zhang et al., but I did not confirm this.
- beta = -0.1988 is within 4e-5 of the critical value -0.198838. f''(0) there is about 0.005, so the digits are sensitive to the exact beta used and to the truncation of the domain.
- I did not look at any other source (Zhang, Salama and others). I stopped after the Asaithambi review.
