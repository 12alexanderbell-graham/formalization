Category: wrong-number
Reader would wrongly believe: at the paper's own CPL toy model (0.245, -0.93, -0.41) the true l0 is -0.809 and the printed one -0.906, i.e. the misprint changes l0 by only 11 % and keeps its sign; the numbers look certified ([✓F2_toy]).
Why it is false: Records.F2_toy certifies true l0 = +0.809 (printed -0.906): the misprint flips the sign of l0 and changes it by 212 %. The minus sign in front of 0.809 is an EN DASH (U+2013), which the number regex ([−-]? = U+2212 or hyphen) does not read as part of the number, so the tagged number is still "0.809".
Expected: ACCEPTED (pair (0.809, F2_toy) unchanged in both check_numbers.py modes; an en dash is not a minus to the extractor but reads as one to a human).
