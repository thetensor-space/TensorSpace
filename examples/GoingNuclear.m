K := Rationals();
A := KMatrixSpace(K, 3, 4);
B := KMatrixSpace(K, 4, 5);
C := KMatrixSpace(K, 3, 5);
F := func< x | x[1]*x[2] >;
T := Tensor([A, B, C], F);
T;


L := LeftNucleus(T);
M := MidNucleus(T);
R := RightNucleus(T);
Dimension(L), Dimension(M), Dimension(R);
D := DerivationAlgebra(T);
Dimension(D);


Omega := KMatrixSpace(K, 47, 47);
Z1 := ZeroMatrix(K, 20, 20);
L2, L_L2 := Induce(L, 2);
L0, L_L0 := Induce(L, 0);
embedL := map< L -> Omega | x :-> 
    DiagonalJoin(<Transpose(x @ L_L2), Z1, Transpose(x @ L_L0)>) >;

Z0 := ZeroMatrix(K, 15, 15);
M2, M_M2 := Induce(M, 2);
M1, M_M1 := Induce(M, 1);
embedM := map< M -> Omega | x :->
    DiagonalJoin(<x @ M_M2, -Transpose(x @ M_M1), Z0>) >;

Z2 := ZeroMatrix(K, 12, 12);
R1, R_R1 := Induce(R, 1);
R0, R_R0 := Induce(R, 0);
embedR := map< R -> Omega | x :->
    DiagonalJoin(<Z2, x @ R_R1, x @ R_R0>) >;

Random(Basis(L)) @ embedL in D;
Random(Basis(M)) @ embedM in D;
Random(Basis(R)) @ embedR in D;

