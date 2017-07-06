t := Tensor(Rationals(), [3, 3, 3], [i : i in [1..27]]);
t;
SystemOfForms(t);
Radical(t);
Image(t);


A := HeisenbergAlgebra(t);
A;
Center(A);
SystemOfForms(Tensor(A))[7..9];


NilCat := TensorCategory([1, 1, 1], {{2,1},{0}});
NilCat;
ChangeTensorCategory(~t, NilCat);
A := HeisenbergAlgebra(t);
A;
Center(A);
A^2;
SystemOfForms(Tensor(A))[4..6];


AlgCat := TensorCategory([1, 1, 1], {{2,1,0}});
AlgCat;
ChangeTensorCategory(~t, AlgCat);
A := HeisenbergAlgebra(t);
A;
SystemOfForms(Tensor(A));
