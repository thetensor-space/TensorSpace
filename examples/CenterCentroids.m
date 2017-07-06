M := MatrixAlgebra(GF(3), 4);
f := ConwayPolynomial(3, 2);
C := CompanionMatrix(f);
I := IdentityMatrix(GF(3), 2);
A := sub< M | [InsertBlock(M!0, X, i, j) : \
    X in [I, C], i in [1, 3], j in [1, 3]] >;
T := CommutatorTensor(A);
T;
gl2 := HeisenbergAlgebra(T);
gl2;


sl2 := gl2/Center(gl2);
sl2;
Center(sl2);
Centroid(sl2);

