@rnd = float< ieee_32, ne >;
x = rnd(xx);
y rnd= x * (1 - x);
z = x * (1 - x);

{ x in [0,1] -> y in [0,0.25] /\ y - z in [-3b-27,3b-27] }

z -> 0.25 - (x - 0.5) * (x - 0.5);
y, y - z $ x;
