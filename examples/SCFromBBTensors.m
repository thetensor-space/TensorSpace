sl2 := MatrixLieAlgebra("A1", GF(7));
V := VectorSpace(GF(7), 2);
left_action := func< x | x[2]*Transpose(Matrix(x[1])) >;
left_action(<sl2!0, V!0>);

t := Tensor([* sl2, V, V *], left_action);
t;


StructureConstants(t);

s := Tensor([3, 2, 2], Eltseq(t));
s;

t eq s;

