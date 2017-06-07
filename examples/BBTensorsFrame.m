Q := Rationals();
U := VectorSpace(Q, 4);
V := VectorSpace(Q, 4);
W := VectorSpace(Q, 1);  // Vector space, not the field Q
Dot := func< x | x[1]*Matrix(4, 1, Eltseq(x[2])) >;


Tensor([U, V, W], Dot);


Cat := AdjointCategory(3, 2, 1);
Cat;

t := Tensor([U, V, W], Dot, Cat);
t;

TensorCategory(t);

