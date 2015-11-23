# The hypotheses are contradictory, but a non-immediate case split is necessary
# to prove it.

y = int<zr>(x);
{ y in [0,2] /\ 3 * y * (y - 1) * (y - 2) in [-1,-1] -> z in [5,5] }
z $ y;
