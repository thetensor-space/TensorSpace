t := Tensor(IdentityMatrix(Rationals(), 4), 2, 1);
s := Tensor(IdentityMatrix(Rationals(), 6), 2, 1);
Z := ZeroMatrix(Rationals(), 4, 6);
M := InsertBlock(Z, IdentityMatrix(Rationals(), 4), 1, 1);
H := Homotopism(t, s, [*M, M, IdentityMatrix(Rationals(), 1)*]);
H;


Domain(H);
Codomain(H);
Maps(H);
TensorCategory(H);


Im := Image(H);
Im;
Ker := Kernel(H);
Ker;

