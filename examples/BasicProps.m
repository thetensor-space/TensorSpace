K := Rationals();
U2 := KMatrixSpace(K, 2, 3);
U1 := VectorSpace(K, 3);
U0 := VectorSpace(K, 2);
mult := func< x | Eltseq(x[1]*Matrix(3,1,Eltseq(x[2]))) >;
T := Tensor([* U2, U1, U0 *], mult);
T;

Parent(T);

Domain(T);

Codomain(T);

Valence(T);

Frame(T);

BaseRing(T);

