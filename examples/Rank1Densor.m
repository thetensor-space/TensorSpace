Fr := [ KMatrixSpace(GF(3),2,3), KMatrixSpace(GF(3),3,2),
    KMatrixSpace(GF(3),2,2) ];
F := func< x | x[1]*x[2] >;
t := Tensor(Fr, F);
t;


D := DerivationAlgebra(t);
Dimension(D) eq 4+9+4-1;


T := Parent(t);
T;
densor := DerivationClosure(T, D);
densor eq sub< T | t >;
