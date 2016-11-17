A := OctonionAlgebra(GF(7),-1,-1,-1);
A;
D := DerivationAlgebra(A);
D.1;
Dimension(D);
SemisimpleType(D);


Z := Center(A);
Z;

L := LeftNucleus(A);
L;
L.1;

L eq MidNucleus(A);
L eq RightNucleus(A);

