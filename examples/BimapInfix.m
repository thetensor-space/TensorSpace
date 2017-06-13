A := MatrixAlgebra(Rationals(), 2);
T := Tensor(A);
T;


M := A![0, 1, 0, 0];
M;
S := M*T;
S;
AsMatrices(S, 1, 0);


M*T*[0, 0, 1, 0];
M*T*VectorSpace(Rationals(), 4);


S := VectorSpace(Rationals(), 4)*T;
S;
S*M;

