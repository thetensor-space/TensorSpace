A := MatrixAlgebra(Rationals(), 3);
t := Tensor(A);
t;
SystemOfForms(t)[1];


s := SymmetricTensor(t);
s;
SystemOfForms(s)[1];

