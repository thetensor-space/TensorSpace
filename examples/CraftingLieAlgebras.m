t := Tensor(Rationals(), [3, 3, 2], &cat[[1,-1,0] : i in [1..6]]);
t := AlternatingTensor(t);
t;
SystemOfForms(t);


L := HeisenbergLieAlgebra(t);
L;
SystemOfForms(Tensor(L))[7..8];


NilCat := TensorCategory([1, 1, 1], {{2,1},{0}});
NilCat;
ChangeTensorCategory(~t, NilCat);
L := HeisenbergLieAlgebra(t);
L;
SystemOfForms(Tensor(L))[4..5];

