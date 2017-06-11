R<x,y> := PolynomialRing(Rationals(),2);
T, p := Polarization(x^2*y);
p;
T;
<[1,0],[1,0],[1,0]> @ T;
<[1,0],[1,0],[0,1]> @ T;

