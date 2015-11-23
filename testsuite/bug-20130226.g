y = 1 - x;
z = x * y;

{ not (x in [0.1,0.9] /\ z in [0.26,1]) }

x -> z / y;
y -> z / x;
