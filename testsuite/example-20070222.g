@rnd = float<x86_80,ne>;

q0 = a * y0;
e0 = 1 + 1b-17 - b * y0;
q1 = q0 + e0 * q0;

eps0 = (y0 - 1 / b) / (1 / b);
err = (q1 - a / b) / (a / b);

{
  @FIX(a, 0) /\ a in [1,65535] /\
  @FIX(b, 0) /\ b in [1,65535] /\
  @FLT(y0, 11) /\ |eps0| <= 0.00211373
->
  err in [0,1] /\ a * err in [0,0.99999] /\
  rnd(q0) = q0 /\ rnd(e0) = e0 /\ rnd(q1) = q1
}

err -> -(eps0 * eps0) + (1 + eps0) * 1b-17     { a <> 0, b <> 0 };

rnd(q1) = q1 $ 1 / b;
