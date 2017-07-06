K := Rationals();
U := KMatrixSpace(K, 2, 2);
V := VectorSpace(K, 2);
mult := func< x | x[1]*x[2] >;
t := Tensor([* V, U, V *], mult);
t;


TensorCategory(t);
Cat := TensorCategory([1, 1, 1], {{2,0},{1}});
Cat;
ChangeTensorCategory(~t, Cat);
TensorCategory(t);
IsCovariant(t);

