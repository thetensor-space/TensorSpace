K := Rationals();
U2 := KMatrixSpace(K, 2, 3);
U1 := VectorSpace(K, 3);
U0 := VectorSpace(K, 2);
mult := func< x | Eltseq(x[1]*Matrix(3,1,Eltseq(x[2]))) >;
t := Tensor([* U2, U1, U0 *], mult);
t;

Parent(t);

Domain(t);

Codomain(t);

Valence(t);

Frame(t);

BaseRing(t);

