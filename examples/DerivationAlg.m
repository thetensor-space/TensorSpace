A := OctonionAlgebra(Rationals(), -1, -1, -1);
A;
D := DerivationAlgebra(A);
D;
SemisimpleType(D);


a := Random(Basis(A));
b := Random(Basis(A));
del := Random(Basis(D));
(a*b)*del eq (a*del)*b + a*(b*del);


J := ExceptionalJordanCSA(A);
J;
D_J := DerivationAlgebra(J);
Dimension(D_J);
SemisimpleType(D_J);

