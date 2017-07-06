R<x,y> := PolynomialRing(Rationals(),2);
t, p := Polarization(x^2*y);
p;
t;
<[1,0],[1,0],[1,0]> @ t;
<[1,0],[1,0],[0,1]> @ t;

