A := MatrixAlgebra(GF(3),25);
f := RandomIrreduciblePolynomial(GF(3),25);
S := sub< A | CompanionMatrix(f) >; // GF(3^25) inside A
T := Tensor(S);
T;
C := Centroid(T);
Dimension(C);
Ngens(C);
