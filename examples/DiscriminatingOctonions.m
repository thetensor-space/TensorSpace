A := OctonionAlgebra(GF(7), -1, -1, -1);
t := Tensor(A);
t;
R<a,b,c,d,e,f,g,h> := PolynomialRing(GF(7), 8);
disc := R!Discriminant(t);
Degree(disc);
IsHomogeneous(disc);
#Terms(disc);


Factorization(disc);

