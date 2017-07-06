K := GF(17);
MS := KMatrixSpace(K, 2, 2);
J := KroneckerProduct(IdentityMatrix(K, 4), MS![0, 1, -1, 0]);
J;

t := Tensor(J, 2, 1);
t;

IsAlternating(t);


V := VectorSpace(K, 8);
symp := func< x | x[1]*J*Matrix(8, 1, Eltseq(x[2])) >;
s := Tensor([V, V], VectorSpace(K, 1), symp);
s;

SystemOfForms(s);

