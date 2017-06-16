A := OctonionAlgebra(GF(7), -1, -1, -1);
T := Tensor(A);
T;
R<a,b,c,d,e,f,g,h> := PolynomialRing(GF(7), 8);
disc := R!Discriminant(T);
Degree(disc);
IsHomogeneous(disc);
#Terms(disc);


Factorization(disc);

