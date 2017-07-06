K := Rationals();
R<x,y,z> := PolynomialRing(K, 3);
f := x^3 + y^3 + z^3 + x*y*z;
t, p := Polarization(f);
p;
t;


IsSymmetric(t);
AsMatrices(t, 3, 1) eq AsMatrices(t, 2, 1);
AsMatrices(t, 3, 1) eq AsMatrices(t, 3, 2);
AsMatrices(t, 3, 1);


IsAlternating(t);
IsAntisymmetric(t);

