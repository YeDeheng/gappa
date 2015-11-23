@rnd = float< ieee_32, zr >;
a = rnd(a_); b = rnd(b_);
{ a in [3.2,3.3] /\ b in [1.4,1.9] ->
  rnd(a - b) = a - b }
