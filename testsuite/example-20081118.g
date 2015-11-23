@rnd = float<ieee_32,ne>;

x = rnd(x_);
y rnd= x * (1 - x*x * 0x28E9p-16);
My   = x * (1 - x*x * 0x28E9p-16);

{
  |x| <= 1 /\
  |My -/ sin_x| <= 1.55e-3
->
  |y -/ sin_x| <= 1.551e-3
}

$ |x| in (1b-100);
