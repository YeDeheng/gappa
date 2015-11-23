@rnd = float<ieee_64,ne>;
x = rnd(x_);
y = rnd(y_);
{ |rnd(x + y) -/ (x + y)| <= 1b-53 }
