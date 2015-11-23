@IEEEdouble = float<ieee_64,ne>;
# Convention 1: uncapitalized variables match the variables in the C code. Other variables begin with a capital letter.
# Convention 2: variables beginning with ``M'' are mathematical ideal.

# $y_h+y_l$ is a double-double (call it $Y_{hl}$)

yh = IEEEdouble(dummy1);
yl = IEEEdouble(dummy2);
Yhl = yh + yl; # There is also an hypothesis stating that $|y_l| < \mathrm{ulp}(y_h)$.

#--------------- Transcription of the C code --------------------------

s3 = IEEEdouble(-1.6666666666666665741e-01); 
s5 = IEEEdouble( 8.3333333333333332177e-03); 
s7 = IEEEdouble(-1.9841269841269841253e-04);

yh2 IEEEdouble=  yh * yh;
ts  IEEEdouble=  yh2 * (s3 + yh2*(s5 + yh2*s7));
r   IEEEdouble=  yl + yh*ts;
s             =  yh + r;   # no rounding, it is the Fast2Sum

#-------- Mathematical definition of what we are approximating --------

My2 = My*My;
Mts = My2 * (s3 + My2*(s5 + My2*s7));
PolySinY = My + My*Mts;

Epsargred = (Yhl - My)/My;           # argument reduction error
Epsapprox = (PolySinY - SinY)/SinY;  # polynomial approximation error
Epsround = (s - PolySinY)/PolySinY;  # rounding errors in the polynomial evaluation
Epstotal = (s - SinY)/SinY;          # total error

# Some definitions to simplify hints
yhts = IEEEdouble(yh*ts);            # just to make the hints lighter
S1 = yh + (yl + yhts);               # remove last round on $s$

#----------------------  The theorem to prove --------------------------
{
 # Hypotheses 
    |yl / yh| <= 1b-53
 /\ |My| in [1b-200, 6.3e-03] # lower bound guaranteed by Kahan-Douglas algorithm
 /\ |Epsargred| <= 2.53e-23
 /\ |Epsapprox| <= 3.7e-22
 /\ |SinY| in [1b-1000,1]

->

 # Goal to prove
    |Epstotal| <= 1b-67
 /\ |r/yh| <= 1
}

# ---------------------- Hints ----------------------------------

$ My in (0);

(yh - Yhl) / Yhl -> 1 / (1 + yl / yh) - 1;

S1 ~ PolySinY;
S1 -> (Yhl + yhts);

(yl + yhts) / yh -> yl / yh + yhts / yh { yh <> 0 };

