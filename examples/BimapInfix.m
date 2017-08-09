A := MatrixAlgebra(Rationals(), 2);
t := Tensor(A);
t;


M := A![0, 1, 0, 0];
M;
s := M*t;
s;
AsMatrices(s, 1, 0);


M*t*[0, 0, 1, 0];
M*t*VectorSpace(Rationals(), 4);


T := VectorSpace(Rationals(), 4)*t;
T;
T*M;

