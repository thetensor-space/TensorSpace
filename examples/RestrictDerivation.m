A := KMatrixSpace(GF(2), 3, 4);
B := KMatrixSpace(GF(2), 4, 2);
C := KMatrixSpace(GF(2), 2, 2);
D := KMatrixSpace(GF(2), 3, 2);
trip := func< x | x[1]*x[2]*x[3] >;
t := Tensor([A, B, C, D], trip);
t;


D := DerivationAlgebra(t);
Dimension(D);
N32 := Nucleus(t, 3, 2);
N32;


Omega_10 := KMatrixSpace(GF(2), 10, 10);
D_vs := sub< KMatrixSpace(GF(2), 30, 30) | Basis(D) >;
D1, pi1 := Induce(D, 1);
D0, pi0 := Induce(D, 0);
res := hom< D_vs -> Omega_10 | 
    [<x, DiagonalJoin(x @ pi1, x @ pi0)> : x in Basis(D)] >;
res;
Kernel(res);

