K := Rationals();
R<x,y,z> := PolynomialRing(K, 3);
f := x^3 + y^3 + z^3 + x*y*z;
T, p := Polarization(f);
p;
T;


IsSymmetric(T);
AsMatrices(T, 3, 1) eq AsMatrices(T, 2, 1);
AsMatrices(T, 3, 1) eq AsMatrices(T, 3, 2);
AsMatrices(T, 3, 1);


IsAlternating(T);
IsAntisymmetric(T);

