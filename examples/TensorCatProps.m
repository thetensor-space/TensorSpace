K := Rationals();
U := KMatrixSpace(K, 2, 2);
V := VectorSpace(K, 2);
mult := func< x | x[1]*x[2] >;
T := Tensor([* V, U, V *], mult);
T;


TensorCategory(T);
Cat := TensorCategory([1, 1, 1], {{2,0},{1}});
Cat;
ChangeTensorCategory(~T, Cat);
TensorCategory(T);
IsCovariant(T);

