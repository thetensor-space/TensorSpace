A := MatrixAlgebra(Rationals(), 3);
T := Tensor(A);
T;
SystemOfForms(T)[1];


S := SymmetricTensor(T);
S;
SystemOfForms(S)[1];

