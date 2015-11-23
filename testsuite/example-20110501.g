x  = float<ieee_64,ne>(dummyx); # x is a double

# Cody-Waite argument reduction
Log2h = 0xb.17217f7d1cp-4; # 42 bits out of 53
InvLog2= 0x1.71547652b82fep0;
kd = int<ne>(float<ieee_64,ne>(x*InvLog2));
t1 float<ieee_64,ne>= x - kd*Log2h;

# prove that t1 is actually equal to T1
T1 = x - kd*Log2h;
{ x in [0.7, 800] -> t1 = T1 }

Log2h ~ 1/InvLog2;
