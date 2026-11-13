Category: wrong-statement (direction, F14 Correct line)
Reader would wrongly believe: F14: the true reverse-flow wall shear lies below the printed −0.005158 (the printed value is too large).
Why it is false: Line: "a reverse-flow solution ... exists, with a wall shear below the printed value by the difference certified below". Lean F14_reversed_wall_shear: `RoundsTo (q 0 - printedFazioRevWall) 6e-7 7`, i.e. q 0 = printed + 6e-7, ABOVE the printed value (generated role: difference(free−printed)).
Expected: ACCEPTED (direction words in Correct are not read; roles only checked next to tagged numbers in prose, none here).
