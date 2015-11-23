R = 1 / d;

r1 fixed<-14,dn>= r0 * (2 - fixed<-16,dn>(d) * r0);
r2 fixed<-30,dn>= r1 * (2 - d * r1);

{ @FIX(d,-24) /\ d in [0.5,1] /\
  @FIX(r0,-8) /\ r0 - R in [-1b-8,1b-8] ->
  r2 - R in ? }

r1 ~ r0 * (2 - d * r0);
r0 * (2 - d * r0) - R -> (r0 - R) * (r0 - R) * -d   { d <> 0 };
r2 ~ r1 * (2 - d * r1);
r1 * (2 - d * r1) - R -> (r1 - R) * (r1 - R) * -d   { d <> 0 };
