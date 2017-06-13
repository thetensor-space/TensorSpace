A := MatrixAlgebra(GF(3), 3);
JacobiID := func< x | x[1]*x[2]*x[3]+x[2]*x[3]*x[1]+x[3]*x[1]*x[2] >;
Cat := TensorCategory([1 : i in [0..3]], {{0..3}});
T, Maps := Tensor([A : i in [0..3]], JacobiID, Cat);
T;
TensorCategory(T);


x := <A.1, A.2, A.2^2>;
x;
x @ T;

phi := Maps[1];
x := <A.1 @ phi, A.2 @ phi, (A.2^2) @ phi>;
x;
x @ T;


x := <A.1, A.2 @ phi, Eltseq(A.2^2)>;
x;
<Type(i) : i in x>;
x @ T;

